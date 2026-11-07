#!/usr/bin/env python3
"""段1′：ソースのスコープから名前候補を作り、kernel検査で一意なものだけ採用。"""
import argparse
import collections
import csv
import hashlib
import json
from pathlib import Path
import re
import sys
import time

import check_declarations as audit

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3] if len(BASE.parents) > 3 else BASE


def mask(text):
    """入れ子コメント・文字列を空白にし、位置と改行は保持する。"""
    out = list(text); depth = 0; quoted = False; i = 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out[i:i+2] = '  '; i += 2; continue
            if pair == '-/': depth -= 1; out[i:i+2] = '  '; i += 2; continue
            if text[i] != '\n': out[i] = ' '
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                out[i:i+2] = [' ' if c != '\n' else '\n' for c in text[i:i+2]]; i += 2; continue
            if text[i] == '"': quoted = False
            if text[i] != '\n': out[i] = ' '
        elif pair == '/-': depth = 1; out[i:i+2] = '  '; i += 2; continue
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out[i:end] = ' ' * (end - i); i = end; continue
        elif text[i] == '"': quoted = True; out[i] = ' '
        i += 1
    return ''.join(out)


def scopes(text):
    frames = []; temporary = []; snapshots = []; declarations = []
    def context():
        parts = []
        for f in frames:
            if f['kind'] == 'absolute': parts = [f['name']]
            elif f['kind'] == 'namespace': parts.append(f['name'])
        namespace = '.'.join(parts)
        opened = [n for f in frames for n in f['opens']] + temporary
        return dict(namespace=namespace, opens=opened)
    frames.append(dict(kind='root', name='', opens=[]))
    for line, code in enumerate(mask(text).splitlines(), 1):
        s = re.sub(r'^(@\[[^]]*\]\s*)+', '', code.strip())
        inline = re.match(r'open\s+(?!scoped\b)(.*?)\s+in\s+(.+)', s)
        if inline:
            temporary.extend(n for n in inline[1].split() if audit.NAME.fullmatch(n))
            s = inline[2]
        snapshots.append(context())
        m = re.match(r'namespace\s+([\w.\']+)\s*$', s)
        if m:
            name = m[1]
            if name.startswith('_root_.'):
                frames.append(dict(kind='absolute', name=name.removeprefix('_root_.'), opens=[]))
            else: frames.append(dict(kind='namespace', name=name, opens=[]))
            continue
        m = re.match(r'(?:(?:noncomputable|public|private)\s+)?section(?:\s+([\w\']+))?\s*$', s)
        if m:
            frames.append(dict(kind='section', name=m[1] or '', opens=[])); continue
        m = re.match(r'end(?:\s+([\w.\']+))?\s*$', s)
        if m:
            if len(frames) > 1: frames.pop()
            temporary = []; continue
        m = re.match(r'open\s+(?!scoped\b)(.*?)\s*(?:in)?\s*$', s)
        if m:
            body = m[1]; is_local = bool(re.search(r'\bin\s*$', s))
            if is_local: body = re.sub(r'\bin\s*$', '', body).strip()
            # open Foo (bar)ではFooだけを候補に使う。scoped/renaming内の名前は推測しない。
            body = re.sub(r'\([^)]*\)', '', body)
            body = re.split(r'\b(?:hiding|renaming)\b', body)[0]
            names = [n for n in body.split() if audit.NAME.fullmatch(n)]
            if is_local: temporary.extend(names)
            else: frames[-1]['opens'].extend(names)
            continue
        m = re.match(r'(?:(?:noncomputable|protected|private|public|unsafe|partial)\s+)*(?:def|abbrev|lemma|theorem|class|structure|axiom|opaque)\s+([\w.\']+)', s)
        if m:
            c = context(); name = m[1]
            declarations.append(dict(line=line, name=name, context=c, private='private' in s[:m.start(1)].split()))
            temporary = []
        elif re.match(r'(?:(?:noncomputable|private|public|unsafe)\s+)*(?:instance|example)\b', s):
            temporary = []
    return snapshots, declarations


def locate(raw):
    ref = audit.reference(raw)
    if ref['source']:
        return ref
    m = re.fullmatch(r'(.+?) @ (IC/[^\s:]+\.lean|HomotopicalAlgebra/[^\s:]+\.lean):(\d+)', raw)
    if m:
        path = ('SerrePositivity/InfinityCategories/' + m[2][3:]) if m[2].startswith('IC/') else 'SerrePositivity/' + m[2]
        ref.update(source=path, source_line=m[3], module='.'.join(Path(path).with_suffix('').parts))
        if audit.NAME.fullmatch(m[1]): ref['declaration'] = m[1]
    return ref


def candidates(ref, text):
    name = ref['declaration']
    if not name or not audit.NAME.fullmatch(name):
        return [], '説明・複数名・匿名instance等は単一名に縮めない'
    snapshots, declarations = scopes(text)
    line = int(ref['source_line'] or 1)
    context = snapshots[min(max(line - 1, 0), len(snapshots) - 1)] if snapshots else dict(namespace='', opens=[])
    leaf = name.split('.')[-1]
    near_private = [d for d in declarations if d['name'].split('.')[-1] == leaf and d['private'] and ref['source_line'] and abs(d['line'] - line) <= 12]
    if near_private: return [], '近傍のprivate宣言は安定した公開名へ推測で補正しない'
    matching = [d for d in declarations if d['name'].split('.')[-1] == leaf and not d['private']]
    # 引用行から12行以内の最寄り宣言を使う。別namespaceの同名宣言まで候補の根拠にしない。
    if matching and ref['source_line']:
        distance = min(abs(d['line'] - line) for d in matching)
        matching = [d for d in matching if abs(d['line'] - line) == distance] if distance <= 12 else []
    contexts = [context] + [d['context'] for d in matching]
    result = {name}
    suffixes = ['.'.join(name.split('.')[-n:]) for n in range(1, min(3, len(name.split('.'))) + 1)]
    if matching:
        full_names = ['.'.join(filter(None, [d['context']['namespace'], d['name']])) for d in matching]
        longest = max((len(s.split('.')) for s in suffixes if any(full == s or full.endswith('.' + s) for full in full_names)), default=1)
        suffixes = [s for s in suffixes if len(s.split('.')) == longest]
    for d in matching:
        result.add('.'.join(filter(None, [d['context']['namespace'], d['name']])))
    for c in contexts:
        ns = c['namespace'].split('.') if c['namespace'] else []
        prefixes = {'.'.join(ns[:n]) for n in range(len(ns) + 1)}
        opened = set(c['opens'])
        for p in list(prefixes):
            for op in c['opens']: opened.add('.'.join(filter(None, [p, op])))
        # open CategoryTheory; open Limitsのような相対openも1段だけ合成する。
        for a in c['opens']:
            for b in c['opens']:
                if a != b: opened.add(a + '.' + b)
        for prefix in prefixes | opened:
            for suffix in suffixes:
                result.add('.'.join(filter(None, [prefix, suffix])))
    return sorted(n for n in result if audit.NAME.fullmatch(n)), '引用行・近傍12行の最寄り同名宣言のスコープと最長一致接尾名を使用'


def prepare(directory):
    if directory.exists(): raise ValueError('既存runを上書きしません')
    original = BASE / 'runs/all-20261107-01'
    plan = json.loads((original / 'plan.json').read_text())
    with (original / 'declaration-results.csv').open() as f:
        csv.field_size_limit(64 * 1024 * 1024)
        states = {r['id']: r for r in csv.DictReader(f)}
    requests = []; probes = {}; cache = {}; sources = {}
    for old in plan['references']:
        state = states[old['id']]['state']
        request = dict(original_id=old['id'], original_raw=old['raw'], original_state=state, candidates=[], rule='')
        if state == 'found':
            requests.append(request); continue
        ref = locate(old['raw']); source = ref['source']
        path = ROOT / ('.lake/packages/mathlib/' + source if source.startswith('Mathlib/') else source)
        if not source or not path.is_file():
            request['rule'] = '出典パスを確定できない'; requests.append(request); continue
        if source not in cache:
            cache[source] = path.read_text(); sources[source] = audit.digest(path)
        names, rule = candidates(ref, cache[source]); request['rule'] = rule
        for name in names:
            probe = audit.reference(f'{name} @ {source}')
            probes[probe['id']] = probe; request['candidates'].append(probe['id'])
        requests.append(request)
    grouped = collections.defaultdict(list)
    for p in probes.values(): grouped[p['module']].append(p['id'])
    modules = sorted(grouped)
    batches = [[module] for module in modules]
    jobs = [dict(id=f'batch-{i+1:04d}', modules=ms, references=[r for m in ms for r in grouped[m]]) for i, ms in enumerate(batches)]
    audit.dump(directory / 'plan.json', dict(schema=1, provenance=audit.provenance(ROOT), resolver_sha256=audit.digest(Path(__file__)), source_hashes=sources, requests=requests, probes=list(probes.values()), jobs=jobs, original_plan=str(original.relative_to(ROOT)), original_results_sha256=audit.digest(original/'declaration-results.csv'), batch_size=1))
    print(json.dumps(dict(original=len(requests), targets=sum(r['original_state']!='found' for r in requests), candidates=len(probes), modules=len(modules), batches=len(jobs)), ensure_ascii=False))


def run(directory, plan, only_modules=(), limit=None):
    if audit.provenance(ROOT) != plan['provenance'] or audit.digest(Path(__file__)) != plan['resolver_sha256']:
        raise ValueError('HEAD・入力・検査スクリプトが変化。新しいrun-dirをprepareする')
    for source, expected in plan['source_hashes'].items():
        path = ROOT / ('.lake/packages/mathlib/' + source if source.startswith('Mathlib/') else source)
        if audit.digest(path) != expected: raise ValueError('source changed: ' + source)
    probes = {r['id']: r for r in plan['probes']}
    unknown=set(only_modules)-{m for job in plan['jobs'] for m in job['modules']}
    if unknown: raise ValueError('計画にないmodule: ' + str(sorted(unknown)))
    count = 0
    for job in plan['jobs']:
        if only_modules and not set(only_modules).intersection(job['modules']): continue
        d = directory / 'modules' / job['id']; metadata = d / 'execution.json'
        if metadata.exists():
            if json.loads(metadata.read_text())['state'] == 'checked': continue
            raise ValueError('中断・失敗の既存試行は上書きしない: ' + str(d))
        if limit is not None and count >= limit: break
        count += 1
        d.mkdir(parents=True)
        text, commands = audit.lean_input(job['modules'][0], [probes[r] for r in job['references']])
        imports = '\n'.join('import ' + m for m in job['modules'])
        text = text.replace('import ' + job['modules'][0], imports, 1).replace('set_option pp.explicit true', 'set_option pp.explicit false\nset_option maxErrors 0')
        for c in commands.values():
            for key in c: c[key] += len(job['modules'])
        (d / 'Check.lean').write_text(text); audit.dump(d / 'commands.json', commands)
        execution = dict(state='started', modules=job['modules'], build_returncode=None, lean_returncode=None)
        audit.dump(metadata, execution)
        while audit.inspect_builds(ROOT, d) == 'build_busy':
            print(job['id'] + ': waiting for SerrePositivity full build', flush=True); time.sleep(10)
        if audit.inspect_builds(ROOT, d) == 'preflight_failed': raise RuntimeError('ps failed')
        attempt = 0
        while True:
            code = audit.call(ROOT, ['zsh','scripts/refactor/with_build_lock.sh','--wait','0','--','lake','build',*job['modules']], d/'build.stdout.txt',d/'build.stderr.txt')
            if code != 75: break
            attempt += 1
            for stream in ('stdout','stderr'): (d/f'build.{stream}.txt').rename(d/f'build.wait-{attempt}.{stream}.txt')
            time.sleep(10)
            while audit.inspect_builds(ROOT,d) == 'build_busy': time.sleep(10)
        execution['build_returncode'] = code
        if code:
            execution['state'] = 'build_failed'
        else:
            execution['state'] = 'checking'; audit.dump(metadata,execution)
            execution['lean_returncode'] = audit.call(ROOT,['lake','env','lean','-DmaxErrors=0','--json',str((d/'Check.lean').relative_to(ROOT))],d/'lean.stdout.jsonl',d/'lean.stderr.txt')
            execution['state'] = 'checked'
        audit.dump(metadata,execution)
        print(job['id'] + ': ' + execution['state'],flush=True)


def resolution_state(original_state, candidates, results):
    successful = [p for p in candidates if results.get(p, {}).get('state') == 'found']
    pending = any(p not in results or results[p].get('state') in {'output_invalid','axioms_unparsed'} or (results[p].get('state') == 'check_failed' and not results[p].get('diagnostics')) for p in candidates)
    state = 'found' if original_state == 'found' else 'pending' if pending else 'renamed' if len(successful) == 1 else 'ambiguous' if len(successful) > 1 else 'manual'
    return state, successful


def parse(directory, plan):
    results = {}; probes = {r['id']:r for r in plan['probes']}
    modules = collections.Counter()
    for job in plan['jobs']:
        d = directory/'modules'/job['id']; path=d/'execution.json'
        if not path.exists(): modules['not_run'] += 1; continue
        execution=json.loads(path.read_text()); modules[execution['state']] += 1
        if execution['state'] != 'checked': continue
        results.update(audit.parse_output((d/'lean.stdout.jsonl').read_text(),(d/'lean.stderr.txt').read_text(),execution['lean_returncode'],json.loads((d/'commands.json').read_text())))
    rows=[]
    original_plan=json.loads((ROOT/plan['original_plan']/'plan.json').read_text())
    original_refs={r['id']:r for r in original_plan['references']}
    for request in plan['requests']:
        state, successful = resolution_state(request['original_state'], request['candidates'], results)
        selected=probes[successful[0]] if state=='renamed' else None
        old=original_refs[request['original_id']]
        resolved_name=selected['declaration'] if selected else old['declaration'] if state=='found' else ''
        resolved_source=selected['source'] if selected else old['source'] if state=='found' else ''
        cited=locate(request['original_raw'])
        citation=(resolved_name+' @ '+resolved_source+(':'+cited['source_line'] if cited['source_line'] else '')) if resolved_name else ''
        rows.append(dict(request,state=state,declarations_new=citation,candidate_count=len(request['candidates']),tested_candidate_count=sum(p in results for p in request['candidates']),declaration_new=resolved_name,source_new=resolved_source,successful_json=json.dumps([probes[p]['declaration'] for p in successful],ensure_ascii=False),extra_axioms_json=json.dumps(results[successful[0]]['extra_axioms'] if selected else [],ensure_ascii=False)))
    audit.write_csv(directory/'resolution-results.csv',rows,['original_id','original_raw','original_state','state','declarations_new','candidate_count','tested_candidate_count','declaration_new','source_new','rule','successful_json','extra_axioms_json'])
    audit.write_csv(directory/'candidate-results.csv',[dict(probes[p],**r,axioms_json=json.dumps(r.get('axioms')),extra_axioms_json=json.dumps(r.get('extra_axioms'))) for p,r in results.items()],['id','declaration','source','state','type','axioms_json','extra_axioms_json','diagnostics'])
    audit.write_csv(directory/'verified-candidates.csv',[dict(probes[p],**r,axioms_json=json.dumps(r.get('axioms')),extra_axioms_json=json.dumps(r.get('extra_axioms'))) for p,r in results.items() if r['state']=='found'],['id','declaration','source','state','type','axioms_json','extra_axioms_json'])
    audit.dump(directory/'manifest.json',dict(provenance=plan['provenance'],resolver_sha256=plan['resolver_sha256'],source_hashes=plan['source_hashes'],plan_sha256=audit.digest(directory/'plan.json'),original_plan=plan['original_plan'],original_results_sha256=plan.get('original_results_sha256'),modules=sum(len(j['modules']) for j in plan['jobs']),candidates=len(plan['probes'])))
    summary=dict(before=dict(collections.Counter(r['original_state'] for r in rows)),after=dict(collections.Counter(r['state'] for r in rows)),batches=dict(modules),candidate_checks=len(results),nonstandard_axiom_candidates=sum(bool(r.get('extra_axioms')) for r in results.values()), selected_nonstandard_axiom_references=sum(bool(json.loads(r['extra_axioms_json'])) for r in rows))
    summary['resolved_total']=summary['after'].get('found',0)+summary['after'].get('renamed',0)
    summary['manual_total']=summary['after'].get('manual',0)+summary['after'].get('ambiguous',0)
    summary['incomplete_total']=summary['after'].get('pending',0)
    audit.dump(directory/'summary.json',summary); print(json.dumps(summary,ensure_ascii=False))
    return summary


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['prepare','run','parse']);p.add_argument('--run-dir',required=True);p.add_argument('--module',action='append',default=[]);p.add_argument('--limit',type=int);a=p.parse_args()
    if a.limit is not None and a.limit < 1: p.error('limitは正の整数')
    if a.action != 'run' and (a.module or a.limit is not None): p.error('--module/--limitはrun専用')
    directory=(BASE/a.run_dir).resolve()
    if not directory.is_relative_to(BASE/'runs'): p.error('run-dirはruns/配下に限定')
    if a.action=='prepare': prepare(directory);return
    plan=json.loads((directory/'plan.json').read_text())
    if a.action=='run': run(directory,plan,a.module,a.limit)
    parse(directory,plan)


if __name__=='__main__': main()
