#!/usr/bin/env python3
"""概要：順序付き targets 配列のモジュール統合。既定は dry-run。

方針：BS の統合方式を一般化し、宣言・証明・namespace・variable を保持する。
規約：--area は統合の所有範囲。外部ファイルは import だけを変更する。
       --check は git 追跡・順序・scope・private・option を検査する。
       move/split は草案の報告用であり、混在計画の --apply は拒否する。
使われ方：merge_modules.py plan.json --area SerrePositivity.DifferentialGraded
          --check --max-lines 1500 --report report.md
保存検査：--snapshot-before before.json --snapshot-after after.json
          （計画なしでも可）。比較規則は compare_snapshots.py に委譲する。
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
import json
from pathlib import Path
import re
import statistics
import subprocess
import sys

from layer_check import code_only, imports, under

ROOT = Path(__file__).resolve().parents[2]
NAME = r"[\w\u0080-\uffff'][\w\u0080-\uffff'.]*"
SCOPE = re.compile(r'^(?:@\[expose\]\s+)?(?:(?:public|private|noncomputable|meta)\s+)*(section|namespace)(?:\s+('+NAME+r'))?\s*$')
HEADER = re.compile(r'^(?:@\[expose\]\s+)?public\s+(?:noncomputable\s+)?section\s*$')
IMPORT = re.compile(r'(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\s+(?:all\s+)?')
BOUNDARIES = set('module prelude import public private meta open namespace section end def abbrev opaque theorem lemma example instance inductive structure class variable variables universe universes noncomputable set_option attribute export initialize syntax macro macro_rules elab deriving in include omit axiom constant mutual local scoped assert_no_sorry assert_not_exists assert_not_imported run_cmd run_elab'.split())


def module_path(module):
    if not isinstance(module, str) or not re.fullmatch(NAME, module) or '..' in module or module.endswith('.'):
        raise ValueError(f'invalid module name: {module!r}')
    return module.replace('.', '/') + '.lean'


def git_files(root):
    result = subprocess.run(['git', 'ls-files', '-z'], cwd=root, capture_output=True, check=True)
    return set(result.stdout.decode().split('\0')) - {''}


def import_commands(text):
    """Offsets in the original source; comments/strings never become commands."""
    mask = code_only(text)
    for match in IMPORT.finditer(mask):
        tokens, position = [], match.end()
        while token := re.match(r'\s*('+NAME+r')', mask[position:]):
            if token[1] in BOUNDARIES:
                break
            start = position + token.start(1)
            tokens.append((start, position + token.end(1), token[1]))
            position += token.end()
        if not tokens:
            raise ValueError('unsupported or empty import command')
        yield match.start(), tokens[-1][1], text[match.start():match.end()], tokens


def replace_ranges(text, changes):
    for start, end, replacement in sorted(changes, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text


def rewrite_imports(text, rename, self_module=None, deletes=()):
    changes, seen = [], set()
    for start, end, prefix, tokens in import_commands(text):
        kept = []
        for a, b, name in tokens:
            new = rename.get(name, name)
            key = (tuple(code_only(prefix).split()[:-1]), new)
            if name in deletes or new == self_module or key in seen:
                continue
            seen.add(key); kept.append((a, b, new))
        if not kept:
            # Retain comments inside a multiline import, but remove its code.
            mask = code_only(text[start:end])
            replacement = ''.join(c if m.isspace() else ' ' for c, m in zip(text[start:end], mask))
            changes.append((start, end, replacement))
        else:
            keep = {a: new for a, _, new in kept}
            changes.extend((a, b, keep.get(a, '')) for a, b, _ in tokens)
    return replace_ranges(text, changes)


def update_scopes(stack, line, label):
    if opened := SCOPE.fullmatch(line):
        kind, name = opened[1], opened[2] or ''
        for part in (name.split('.') if kind == 'namespace' else [name]):
            stack.append((kind,part))
    elif closed := re.fullmatch(r'end(?:\s+('+NAME+r'))?', line):
        names = closed[1].split('.') if closed[1] else ['']
        if len(stack)<len(names): raise ValueError(f'{label}: unmatched end')
        actual = [name for _,name in stack[-len(names):]]
        if actual != names:
            raise ValueError(f'{label}: mismatched end {closed[1]} (opened {actual!r})')
        del stack[-len(names):]


def scope_balance(body, label):
    stack=[]
    for line in code_only(body).splitlines(): update_scopes(stack,line.strip(),label)
    if any(name for _,name in stack):
        raise ValueError(f'{label}: unclosed named section/namespace: {stack}')
    return len(stack)


def private_names(body):
    stack, result = [], []
    for line in code_only(body).splitlines():
        line=line.strip()
        update_scopes(stack,line,'private scan')
        m = re.match(r'(?:@\[.*?\]\s*)?(?:(?:noncomputable|unsafe)\s+)*private\s+(?:def|abbrev|theorem|lemma|opaque|instance|structure|class|inductive)\s+('+NAME+r')', line)
        if m:
            namespace=[n for kind,n in stack if kind=='namespace']
            result.append('.'.join(namespace+[m[1]]))
    return result


@dataclass
class Part:
    module: str
    text: str
    imports: list[str]
    universes: list[str]
    header: str
    body: str
    doc: str
    warnings: list[str]


def remove_header_command(text, mask, start, end):
    # Drop a header-only physical line, preserving any comments on that line.
    original=text[start:end]
    clean=mask[start:end]
    if original.strip()==clean.strip() and (end==len(text) or text[end]=='\n'):
        return start,min(len(text),end+1),''
    return start,end,''.join(c if m.isspace() else ' ' for c,m in zip(original,clean))


def parse_part(module, text, renames=None):
    mask = code_only(text)
    changes, imps, universes, warnings = [], [], [], []
    for start, end, _, tokens in import_commands(text):
        imps.extend(t[2] for t in tokens)
        # Header comments remain at their original locations in the body.
        changes.append(remove_header_command(text,mask,start,end))
    for match in re.finditer(r'(?m)^module[ \t\r]*$', mask):
        changes.append(remove_header_command(text,mask,match.start(),match.end()))
    # Extract the first module docstring, using nesting rather than a non-greedy regex.
    doc = ''
    for match in re.finditer(r'/\-!', text):
        start = match.start()
        if code_only(text[:start]).strip().endswith('/'):
            continue
        # A candidate inside an earlier comment/string is not a module docstring.
        try: code_only(text[:start])
        except ValueError: continue
        depth, end = 1, start+3
        while depth and end < len(text):
            if text.startswith('/-',end): depth += 1; end += 2
            elif text.startswith('-/',end): depth -= 1; end += 2
            else: end += 1
        doc = text[start:end]
        changes.append((start,end,'')); break
    header = None
    for match in re.finditer(r'(?m)^.*$', mask):
        line = match[0].strip()
        if HEADER.fullmatch(line):
            header = line
            changes.append(remove_header_command(text,mask,match.start(),match.end()))
            break
        if re.match(r'(?:namespace|(?:private |noncomputable )?(?:def|theorem|lemma|instance))\b',line):
            break
    if header is None:
        header = 'section'
        warnings.append(f'{module}: no public section; wrapped in non-public section')
    for match in re.finditer(r'(?m)^[ \t]*universes?[ \t]+([^\n]+)$', mask):
        # Universe declaration order determines declaration level-parameter order.
        # Keep each source's commands verbatim inside its own section.
        universes.append(text[match.start():match.end()])
        changes.append((match.start(), min(len(text), match.end()+1), ''))
    body = replace_ranges(text, changes)
    # An explicit end of the original outer anonymous public section becomes our end.
    try:
        unclosed = scope_balance(body,module)
    except ValueError as exc:
        if header != 'section' and str(exc).endswith('unmatched end'):
            ends = list(re.finditer(r'(?m)^end[ \t]*$',code_only(body)))
            if not ends: raise
            last = ends[-1]; body = body[:last.start()]+body[last.end():]
            unclosed = scope_balance(body,module)
        else: raise
    known = private_names(body)
    for old,new in (renames or {}).items():
        if not re.fullmatch(NAME,old) or not re.fullmatch(NAME,new):
            raise ValueError(f'{module}: invalid private rename')
        if not any(n == old or n.endswith('.'+old) for n in known):
            raise ValueError(f'{module}: private rename not found: {old}')
        masked = code_only(body)
        matches = list(re.finditer(r"(?<![\w.'])"+re.escape(old)+r"(?![\w'])",masked))
        body = replace_ranges(body, [(m.start(),m.end(),new) for m in matches])
    if unclosed:
        warnings.append(f'{module}: close {unclosed} anonymous section(s)')
    body = body.strip('\n') + '\n' + 'end\n'*unclosed
    return Part(module,text,list(dict.fromkeys(imps)),universes,header,body,doc,warnings)


def render_group(entry, parts, rename):
    dest = entry['module']
    imps = list(dict.fromkeys(rename.get(i,i) for p in parts for i in p.imports if rename.get(i,i)!=dest))
    out = 'module\n\n'+''.join('public import '+i+'\n' for i in imps)
    out += '\n/-!\n'+entry['docstring'].strip()+'\n-/\n'
    names = Counter(p.module.rsplit('.',1)[-1] for p in parts)
    for p in parts:
        stem = p.module.rsplit('.',1)[-1]
        if names[stem]>1: stem = p.module.replace('.','_')
        out += f'\n/-! ## {p.module.rsplit(".",1)[-1]}（旧 {module_path(p.module)}） -/\n'
        if p.doc: out += '\n'+p.doc+'\n'
        out += f'\n{p.header} {stem}\n'
        if p.universes: out += '\n'.join(p.universes)+'\n'
        out += f'\n{p.body}\nend {stem}\n'
    return out, imps


def analyze(root, plan, areas, scope, max_lines=None):
    if not isinstance(plan,list): raise ValueError('targets must be an array')
    tracked = git_files(root)
    merge, deferred, sources, dests, deleted, stubs = [], [], {}, set(), set(), set()
    for row in plan:
        if not isinstance(row,dict) or row.get('action') not in ('merge','move','split'):
            raise ValueError('expected merge/move/split entry')
        module_path(row.get('module'))
        if row['action'] != 'merge':
            module_path(row.get('dest'))
            if module_path(row['module']) not in tracked: raise ValueError('untracked source: '+row['module'])
            if not (root/module_path(row['module'])).is_file(): raise ValueError('missing source: '+row['module'])
            if row['action']=='split' and not row.get('moved'): raise ValueError('split requires moved declarations')
            deferred.append(row); continue
        dest = row['module']
        if dest in dests: raise ValueError('duplicate destination: '+dest)
        dests.add(dest)
        if not isinstance(row.get('sources'),list) or not row['sources']: raise ValueError('empty sources: '+dest)
        if not isinstance(row.get('docstring'),str) or not row['docstring'].strip(): raise ValueError('missing docstring: '+dest)
        for mod in [dest,*row['sources'],*row.get('deletes',[])]:
            path = module_path(mod)
            if not any(under(mod,a) for a in areas): raise ValueError('outside --area: '+mod)
            if mod!=dest or mod in row['sources']:
                if path not in tracked: raise ValueError('untracked source: '+mod)
                if not (root/path).is_file(): raise ValueError('missing source: '+mod)
        if (root/module_path(dest)).exists() and dest not in row['sources']: raise ValueError('destination exists: '+dest)
        for src in row['sources']:
            if src in sources: raise ValueError('duplicate source: '+src)
            sources[src] = dest
        privs = row.get('private_renames',{})
        if not isinstance(privs,dict) or set(privs)-set(row['sources']): raise ValueError('private_renames outside sources')
        if any(not isinstance(v,dict) for v in privs.values()): raise ValueError('invalid private_renames')
        deleted.update(row.get('deletes',[])); stubs.update(row.get('stubs',[])); merge.append(row)
    if deleted & (sources.keys() | dests): raise ValueError('deleted module also merged')
    if not stubs<=sources.keys() or stubs & dests: raise ValueError('stubs must be removed sources, not destinations')
    graph, originals = {}, {}
    # Include untracked consumers as well: they must not be broken or silently overwritten.
    files = subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=root).decode().split('\0')
    for rel in sorted(set(files)):
        if not rel.endswith('.lean') or not (root/rel).is_file(): continue
        originals[rel]=(root/rel).read_bytes().decode('utf-8')
        graph[rel[:-5].replace('/','.')]=imports(originals[rel])
    built, rows, warnings = {}, [], []
    for row in merge:
        dest = row['module']; order={s:i for i,s in enumerate(row['sources'])}
        parts=[parse_part(s,originals[module_path(s)],row.get('private_renames',{}).get(s)) for s in order]
        names, options = {}, defaultdict(lambda:defaultdict(list))
        local=[]
        for p in parts:
            for dep in p.imports:
                if dep in order and order[dep]>=order[p.module]: raise ValueError(f'import order: {p.module} imports later source {dep}')
                if dep in deleted: raise ValueError(f'deleted module still imported: {p.module} -> {dep}')
            for name in private_names(p.body):
                if name in names: raise ValueError(f'private collision: {dest}: {name} in {names[name]} and {p.module}')
                names[name]=p.module
            for option in re.finditer(r'(?m)^\s*set_option\s+(\S+)\s+(.+?)\s*$',code_only(p.body)):
                if not option[2].endswith(' in'): options[option[1]][option[2]].append(p.module)
            local.extend(p.warnings)
        for name,values in options.items():
            if len(values)>1: local.append(f'set_option {name}: '+', '.join(values)+' (isolated by source section)')
        built[dest],imps=render_group(row,parts,sources)
        lines=len(built[dest].splitlines())
        if max_lines and lines>max_lines: local.append(f'max-lines: {lines} > {max_lines}')
        consumers=sorted(n for n,deps in graph.items() if n not in order and deps & order.keys())
        rows.append({'module':dest,'sources':len(parts),'source_lines':sum(len(p.text.splitlines()) for p in parts),'lines':lines,'imports':len(imps),'importers':len(consumers),'warnings':local})
        warnings.extend(local)
    edits={}
    for rel,text in originals.items():
        mod=rel[:-5].replace('/','.')
        if mod in sources or mod in deleted: continue
        deps=graph[mod]; matched=any(re.search(s,rel) for s in scope)
        hit=deps & deleted
        if hit and not (matched and rel.startswith('scripts/')): raise ValueError(f'deleted modules still imported: {rel}: {sorted(hit)}')
        unavailable={d for d in deps & sources.keys() if sources[d]!=d and d not in stubs}
        if unavailable and not matched: raise ValueError(f'importers outside rewrite scope need stubs: {rel}: {sorted(unavailable)}')
        if matched and (deps & sources.keys() or hit):
            changed=rewrite_imports(text,sources,mod,deleted)
            if changed!=text: edits[rel]=changed
    changed=set(sources)|set(built)|deleted|{r[:-5].replace('/','.') for r in edits}
    for row in deferred: changed.update([row['module'],row['dest']])
    reverse=defaultdict(set)
    for n,deps in graph.items():
        for dep in deps: reverse[dep].add(n)
    downstream=set(changed); pending=deque(changed)
    while pending:
        for n in reverse[pending.popleft()]-downstream: downstream.add(n);pending.append(n)
    edges=Counter()
    for n,deps in graph.items():
        if any(under(n,a) for a in areas) or n.startswith('scripts.') or n.startswith('SerrePositivity.Archive.'): continue
        group=n.split('.')[1] if n.startswith('SerrePositivity.') else n
        edges[group]+=sum(any(under(d,a) for a in areas) for d in deps)
    return {'rows':rows,'warnings':warnings,'deferred':deferred,'built':built,'edits':edits,'removed':sorted((sources.keys()-dests)|deleted),'stubs':{s:sources[s] for s in stubs},'external_area_edges':dict(sorted(edges.items())),'downstream':sorted(n for n in downstream if n in graph and n.startswith('SerrePositivity') and not n.startswith('SerrePositivity.Archive.')),'tracked':tracked,'graph':graph}


def report(result):
    rows=result['rows']; sizes=[r['lines'] for r in rows]
    out=['# モジュール統合 dry-run','',f'統合先 {len(rows)}、元 {sum(r["sources"] for r in rows)} 本。move/split 草案 {len(result["deferred"])} 件は未適用。']
    if sizes: out += [f'生成行数：最小 {min(sizes)}、中央値 {statistics.median(sizes):g}、平均 {statistics.mean(sizes):.1f}、最大 {max(sizes)}。']
    out += ['', '| 統合先 | 元本数 | 元行数 | 生成行数 | import 和 | 外部 importer | 警告数 |','| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
    for r in rows: out.append(f'| `{r["module"]}` | {r["sources"]} | {r["source_lines"]} | {r["lines"]} | {r["imports"]} | {r["importers"]} | {len(r["warnings"])} |')
    out += ['', '## 警告','']
    for row in rows:
        if row['warnings']:
            out += ['### `'+row['module']+'`','']+[f'- {w}' for w in row['warnings']]+['']
    out += ['', '## 対象領域の外からの import 辺（Archive・scripts を除く現行ソース）','']
    out += [f'- {k}: {v}' for k,v in result['external_area_edges'].items() if v]
    n=len(result['downstream'])
    out += ['',f'合計 {sum(result["external_area_edges"].values())} 辺。', '', '## 下流見積もり','',f'統合元・D3 移動元/先・import 書換利用元の逆閉包：{n} 本（現存本番ソース、Archive を除く）。単独 1.0–1.5 秒/本なら {n/60:.1f}–{n*1.5/60:.1f} 分。監査時間は別。',f'import のみの書換候補 {len(result["edits"])} ファイル。', '', '## move/split 草案','']
    out += [f'- {r["action"]}: `{r["module"]}` → `{r["dest"]}`。{r.get("note","")}' for r in result['deferred']]
    return '\n'.join(out)+'\n'


def apply(root,result):
    if result['deferred']: raise ValueError('mixed move/split draft: use their tools first and supply a merge-only plan')
    owned=[module_path(m) for m in result['removed']+list(result['built'])]+list(result['edits'])
    if subprocess.check_output(['git','status','--porcelain','--',*owned],cwd=root):
        raise ValueError('refuse to apply over dirty sources/destinations/importers')
    # All semantic and path checks precede the first mutation.
    if result['removed']:
        subprocess.run(['git','rm','--',*[module_path(m) for m in result['removed']]],cwd=root,check=True,stdout=subprocess.DEVNULL)
    for mod,text in result['built'].items():
        path=root/module_path(mod);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(text.encode('utf-8'))
    for rel,text in result['edits'].items(): (root/rel).write_bytes(text.encode('utf-8'))
    for mod,dest in result['stubs'].items():
        path=root/module_path(mod);path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(f'module\n\npublic import {dest}\n\n/-! 互換用の転送。宣言の本体は `{dest}` に統合した。 -/\n')


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('plan',nargs='?',type=Path);p.add_argument('--root',type=Path,default=ROOT)
    p.add_argument('--area',action='append',default=[]);p.add_argument('--rewrite-scope',action='append')
    mode=p.add_mutually_exclusive_group();mode.add_argument('--check',action='store_true');mode.add_argument('--apply',action='store_true')
    p.add_argument('--max-lines',type=int);p.add_argument('--report',type=Path)
    p.add_argument('--snapshot-before',type=Path);p.add_argument('--snapshot-after',type=Path)
    a=p.parse_args(argv)
    try:
        if bool(a.snapshot_before)!=bool(a.snapshot_after): raise ValueError('both snapshot paths are required')
        if a.snapshot_before:
            rc=subprocess.call([sys.executable,str(Path(__file__).with_name('compare_snapshots.py')),str(a.snapshot_before),str(a.snapshot_after)])
            if rc: return rc
        if a.plan is None:
            if not a.snapshot_before: raise ValueError('plan or snapshots required')
            return 0
        if not a.area: raise ValueError('--area is required')
        for area in a.area: module_path(area)
        if a.max_lines is not None and a.max_lines<1: raise ValueError('--max-lines must be positive')
        scope=a.rewrite_scope or [r'^SerrePositivity(?:/.*)?\.lean$',r'^scripts/.*\.lean$']
        for regex in scope: re.compile(regex)
        result=analyze(a.root.resolve(),json.loads(a.plan.read_text()),a.area,scope,a.max_lines)
        if a.report: a.report.write_text(report(result))
        if a.apply: apply(a.root.resolve(),result)
        print(json.dumps({'merge_targets':len(result['rows']),'sources':sum(r['sources'] for r in result['rows']),'warnings':len(result['warnings']),'deferred':len(result['deferred']),'rewrites':len(result['edits']),'applied':a.apply}))
        return 0
    except (ValueError,OSError,KeyError,TypeError,subprocess.CalledProcessError) as exc:
        print('merge_modules: error: '+str(exc),file=sys.stderr);return 1


if __name__=='__main__': raise SystemExit(main())
