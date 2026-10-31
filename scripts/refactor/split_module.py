#!/usr/bin/env python3
"""概要：宣言をバイト単位で保存して Lean モジュールを分割する。
方針：型・証明を含む elaborated な依存関係で import の方向を決める。
規約：曖昧な構文・双方向依存・古い snapshot は変更前に拒否する。
使われ方：module dest --moved NAME... [--snapshot FILE] [--dry-run | --apply]。
"""
import argparse
import difflib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import layer_check as lc
from lean_source import check_attribute_dependencies, transient_names, declaration_owner, Unsupported, parse_source, render, dependency_directions, uses_names, add_import, read_source, write_source, owner

ROOT = Path(__file__).resolve().parents[2]


def module_path(root, name):
    if not isinstance(name, str) or not re.fullmatch(r"SerrePositivity(?:\.[\w']+)*", name):
        raise ValueError('invalid project module: '+str(name))
    path = root / (name.replace('.', '/')+'.lean')
    if not path.resolve().is_relative_to(root.resolve()): raise ValueError('module escapes root')
    return path


def obtain_snapshot(root, module):
    subprocess.run(['lake', 'build', module], cwd=root, check=True)
    out = root/'.lake/verify'; out.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='split-snapshot-', dir=out) as directory:
        target = Path(directory)/'snapshot.json'
        subprocess.run(['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                        '--modules',module,'--output',str(target)],cwd=root,check=True)
        return json.loads(target.read_text())


def module_doc(text, replacement=None):
    match=re.search(r'(?m)^/-!',text)
    start=match.start() if match else -1
    if start < 0:
        at=0
        match=re.search(r'(?m)^module[^\n]*\n',text)
        if match:at=match.end()
        headers=list(re.finditer(r'(?m)^(?:public |private |meta )*import[^\n]*\n',lc.code_only(text)))
        if headers:at=headers[-1].end()
        return text[:at]+'\n/-!\n'+(replacement or '分割で生成：docstring を書き直すこと')+'\n-/\n'+text[at:]
    pos=start+2;depth=1
    while pos<len(text) and depth:
        if text.startswith('/-',pos):depth+=1;pos+=2
        elif text.startswith('-/',pos):depth-=1;pos+=2
        else:pos+=1
    if depth:raise ValueError('unclosed module docstring')
    content=replacement if replacement is not None else '分割で生成：docstring を書き直すこと\n'+text[start+3:pos-2].lstrip('\r\n')
    if replacement is not None and ('/-' in content or '-/' in content):raise ValueError('module doc must be plain comment content without delimiters')
    return text[:start]+'/-!\n'+content.rstrip()+'\n-/'+text[pos:]


def prepare(root, module, dest, moved, snapshot, graph=None, doc=None):
    src, dst = module_path(root,module), module_path(root,dest)
    if module == dest: raise ValueError('source equals destination')
    original = read_source(src)
    if dst.exists() and lc.code_only(read_source(dst)).strip() not in ('', 'module'):
        raise ValueError('destination is not an empty scaffold: '+dest)
    source = parse_source(original, str(src), snapshot=snapshot, module=module)
    moved = set(moved)
    if not moved or moved - source.declarations.keys():
        raise ValueError('empty or unknown moved declarations: '+repr(sorted(moved-source.declarations.keys())))
    matching = [r for r in snapshot.get('sources',[]) if r['module']==module and r['source']==original]
    if not matching: raise ValueError('snapshot source does not match; rebuild and snapshot before splitting')
    rows = [r for r in snapshot['declarations'] if r['module']==module]
    local_snapshot = {**snapshot,'declarations':rows}
    forward, backward = dependency_directions(source, moved, local_snapshot)
    if forward and backward:
        raise Unsupported('bidirectional dependency; split would create an import cycle: '+repr({'moved_to_keep':forward,'keep_to_moved':backward}))
    check_attribute_dependencies(source, moved)
    kept = source.declarations.keys()-moved
    old_text, new_text = render(source,kept,side='keep'), render(source,moved,side='moved')
    if forward: new_text = add_import(new_text,module)
    if backward: old_text = add_import(old_text,dest)
    # Byte-for-byte checks also cover attached docstrings, attributes, and local scopes.
    for name,index in source.declarations.items():
        fragment = source.commands[index].text
        rendered = new_text if name in moved else old_text
        if fragment not in rendered: raise AssertionError('declaration changed: '+name)
    new_text=module_doc(new_text,doc)
    changes = {module:{'before':original,'after':old_text},dest:{'before':read_source(dst) if dst.exists() else None,'after':new_text}}
    if graph is None:
        config=json.loads((ROOT/'scripts/refactor/layers.json').read_text())
        graph,_=lc.read_graph(root,config)
    implicit = any(declaration_owner(r, source.declarations, {x['name']:x for x in rows}) in moved and
                   (r['attributes']['simp'] or r['attributes']['instance_priority'] is not None) for r in rows)
    for consumer,deps in sorted(graph.items()):
        if consumer==module or module not in deps: continue
        path=root/(consumer.replace('.','/')+'.lean')
        text=read_source(path)
        public_export = bool(re.search(r'(?m)^\s*public\s+import\s+(?:all\s+)?'+re.escape(module)+r'(?:\s|$)',lc.code_only(text)))
        if uses_names(text,moved) or implicit or public_export:
            changes[consumer]={'before':text,'after':add_import(text,dest)}
    return {'module':module,'dest':dest,'moved':sorted(moved),'keep':sorted(kept),
            'dependencies':{'moved_to_keep':forward,'keep_to_moved':backward},
            'transient':transient_names(local_snapshot),
            'declaration_modules':{n:dest if n in moved else module for n in source.declarations},
            'changes':changes}


def diff(plan):
    return ''.join(''.join(difflib.unified_diff((v['before'] or '').splitlines(keepends=True),v['after'].splitlines(keepends=True),
                    fromfile=m.replace('.','/')+'.lean',tofile=m.replace('.','/')+'.lean'))
                   for m,v in sorted(plan['changes'].items()))


def apply(root,plan):
    for mod,change in plan['changes'].items():
        path=root/(mod.replace('.','/')+'.lean')
        current=read_source(path) if path.exists() else None
        if current!=change['before']: raise ValueError('source changed during planning: '+mod)
    for mod,change in plan['changes'].items():
        path=root/(mod.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True)
        write_source(path, change['after'])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module');parser.add_argument('dest');parser.add_argument('--moved',nargs='+',required=True)
    parser.add_argument('--snapshot',type=Path);parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--prune-imports',action='store_true')
    parser.add_argument('--module-doc',type=Path,help='UTF-8 plain text inside the new module docstring')
    mode=parser.add_mutually_exclusive_group();mode.add_argument('--dry-run',action='store_true');mode.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    try:
        snapshot=json.loads(args.snapshot.read_text()) if args.snapshot else obtain_snapshot(args.root,args.module)
        plan=prepare(args.root,args.module,args.dest,args.moved,snapshot,doc=read_source(args.module_doc) if args.module_doc else None)
        if args.prune_imports:
            from prune_imports import prune_plan
            plan=prune_plan(args.root,plan,snapshot,apply_changes=args.apply)
        print(diff(plan),end='')
        if args.output: args.output.write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
        if args.apply and not args.prune_imports: apply(args.root,plan)
        print(('APPLIED' if args.apply else 'DRY RUN')+f": {len(plan['moved'])} declarations; {len(plan['changes'])} files")
        return 0
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.CalledProcessError) as exc:
        print('split_module: STOP: '+str(exc),file=sys.stderr);return 1


if __name__=='__main__':sys.exit(main())
