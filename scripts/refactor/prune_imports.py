"""Limit import minimization to the two split files; validate their downstream closure."""
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

import layer_check as lc
from lean_source import read_source, write_source, parse_source, owner
from compare_snapshots import compare

IMPORT = re.compile(r'(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+[\w.]+[ \t]*(?:\r?\n|$)')


def replace_imports(text, modules):
    mask=lc.code_only(text)
    spans=list(IMPORT.finditer(mask))
    if {lc.imports(mask[m.start():m.end()]).pop() for m in spans} != lc.imports(text):
        raise ValueError('pruning requires one simple import per line')
    newline='\r\n' if '\r\n' in text else '\n'
    public=bool(re.search(r'(?m)^module\s*$',mask))
    expected=r'public[ \t]+import[ \t]+' if public else r'import[ \t]+'
    if any(not re.match(expected,m[0].lstrip()) for m in spans):
        raise ValueError('pruning requires public imports in module files, or ordinary imports in legacy files; private/meta/all imports are unsupported')
    lines=''.join(('public import ' if public else 'import ')+m+newline for m in sorted(modules))
    if not spans: raise ValueError('pruning requires an import header')
    for m in reversed(spans[1:]): text=text[:m.start()]+text[m.end():]
    return text[:spans[0].start()]+lines+text[spans[0].end():]


def affected_modules(graph, seeds):
    found=set(seeds)
    while True:
        added={n for n,ds in graph.items() if ds & found}-found
        if not added: break
        found |= added
    return sorted(n for n in found if n=='SerrePositivity' or n.startswith('SerrePositivity.'))


def preservation_dependencies(snapshot, changes, module):
    """Retain dependencies of changed declarations and their generated auxiliaries."""
    names={r['name'] for r in changes}
    rows=[r for r in snapshot['declarations'] if r['name'] in names or r['parent'] in names]
    if any('used_modules' not in r for r in rows):
        raise ValueError('regenerate the snapshot: used_modules is required for preservation-aware pruning')
    return {m for r in rows for m in r['used_modules'] if m!=module}


def prune_plan(root, plan, snapshot, apply_changes=False):
    """Temporarily elaborate the plan even in dry-run; always restore on failure."""
    config=json.loads((root/'scripts/refactor/layers.json').read_text())
    graph,_=lc.read_graph(root,config)
    modules=[plan['module'],plan['dest']]
    if plan['dependencies']['keep_to_moved']: modules.reverse()
    affected=affected_modules(graph,set(modules))
    directory=Path(tempfile.mkdtemp(prefix='prune-',dir=root/'.lake/verify'))
    records=[]
    report={'directory':str(directory),'commands':records,'modules':{},'affected_modules':affected,
            'preservation_checks':[]}
    def path(m):return root/(m.replace('.','/')+'.lean')
    def save(): (directory/'results.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    def run(label,args,expected_failure=False):
        start=time.monotonic();log=directory/(str(len(records))+'-'+label+'.log')
        with log.open('w') as output:
            rc=subprocess.call(args,cwd=root,stdout=output,stderr=subprocess.STDOUT)
        records.append({'label':label,'command':args,'exit_code':rc,'seconds':round(time.monotonic()-start,3),'log':str(log)})
        save()
        if rc and not expected_failure:raise RuntimeError('prune build failed: '+str(log))
        return rc,log.read_text()
    def build_all(label,targets):
        # Build maximal affected targets; their dependency closure covers the rest.
        selected=set(targets)
        imported=set().union(*(graph.get(m,set()) & selected for m in selected))
        tips=sorted(selected-imported)
        if not tips:tips=sorted(selected)
        for i in range(0,len(tips),100):run(label+'-'+str(i//100),['lake','build',*tips[i:i+100]])
    success=False
    try:
        for m,c in plan['changes'].items():
            p=path(m)
            if (read_source(p) if p.exists() else None)!=c['before']:raise ValueError('source changed: '+m)
        for m,c in plan['changes'].items():
            path(m).parent.mkdir(parents=True,exist_ok=True);write_source(path(m),c['after'])
        run('unpruned-build',['lake','build',*modules])
        for m in modules:
            baseline={**snapshot,'declarations':[r for r in snapshot['declarations']
                if plan['declaration_modules'].get(owner(r['name'],plan['declaration_modules']))==m]}
            def preserved(label):
                run(label+'-build',['lake','build',m])
                target=directory/(str(len(records))+'-snapshot.json')
                run(label+'-snapshot',['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                    '--modules',m,'--output',str(target)])
                result=compare(baseline,json.loads(target.read_text()))
                report['preservation_checks'].append({'module':m,'label':label,'result':result,
                                                      'snapshot':str(target)})
                save()
                return result
            text=read_source(path(m));before=sorted(lc.imports(text))
            diagnostic=replace_imports(text,set(before)|{'Mathlib.Tactic.Linter.MinImports'})
            matches=list(IMPORT.finditer(lc.code_only(diagnostic)))
            at=matches[-1].end()
            diagnostic=diagnostic[:at]+'\n#import_bumps\n'+diagnostic[at:]+'\n#min_imports\n'
            try:
                write_source(path(m),diagnostic)
                _,output=run('min-imports',['lake','env','lean',str(path(m))])
            finally:write_source(path(m),text)
            if 'Counting imports from here.' not in output:raise ValueError('minImports did not run')
            unneeded=set(re.findall(r"unneeded import '([\w.]+)'",output))
            additions=set(re.findall(r'(?m)^(?:public )?import ([\w.]+)$',output))
            candidates=(set(before)-unneeded)|additions
            candidate=replace_imports(text,candidates)
            write_source(path(m),candidate)
            rc,output=run('candidate',['lake','env','lean',str(path(m))],True)
            removed_opens=[]
            if rc:
                unavailable=set(re.findall(r'unknown namespace `([^`]+)`',output))
                parsed=parse_source(text)
                for command in reversed(parsed.commands):
                    if command.kind!='context':continue
                    mask=lc.code_only(command.text)
                    edits=[]
                    for match in re.finditer(r'(?m)^open ([\w. ]+)\r?$',mask):
                        words=match[1].split()
                        dropped=set(words)&unavailable
                        if dropped:
                            kept=[w for w in words if w not in dropped]
                            edits.append((match.start(),match.end(),'open '+' '.join(kept) if kept else ''))
                            removed_opens.extend(sorted(dropped))
                    fragment=command.text
                    for a,b,value in reversed(edits):fragment=fragment[:a]+value+fragment[b:]
                    text=text[:command.start]+fragment+text[command.end:]
                if not removed_opens:raise RuntimeError('minImports candidate failed; see '+str(directory))
                candidate=replace_imports(text,candidates);write_source(path(m),candidate)
                run('candidate-without-unused-open',['lake','env','lean',str(path(m))])
            preservation=preserved('candidate')
            if preservation['status']!='PASS':
                # Import reduction can change elaboration even when Lean accepts it.
                # Add baseline declaration dependencies, then minimize subject to
                # the unchanged preservation check, including auxiliary types.
                candidates |= preservation_dependencies(baseline,preservation['changes'],m)
                candidate=replace_imports(text,candidates);write_source(path(m),candidate)
                run('candidate-preserving-dependencies',['lake','env','lean',str(path(m))])
                if preserved('candidate-preserving-dependencies')['status']!='PASS':
                    raise RuntimeError('cannot preserve declarations while pruning; see '+str(directory))
            # Reach an inclusion-minimal set. Revisit failures after each removal,
            # since typeclass/notation choices can depend on the available imports.
            while True:
                removed=False
                for imp in sorted(candidates):
                    trial=replace_imports(text,candidates-{imp})
                    write_source(path(m),trial)
                    rc,_=run('remove-import',['lake','env','lean',str(path(m))],True)
                    if rc==0 and preserved('remove-import')['status']=='PASS':
                        candidates.remove(imp);candidate=trial;removed=True;break
                if not removed:break
            write_source(path(m),candidate)
            plan['changes'][m]['after']=candidate
            report['modules'][m]={'before':before,'after':sorted(candidates),'removed_unused_opens':removed_opens}
            run('pruned-build',['lake','build',m])
        build_all('downstream-build',affected)
        success=True;report['status']='PASS';save()
        plan['pruning']=report
        return plan
    finally:
        if not success or not apply_changes:
            for m,c in plan['changes'].items():
                if c['before'] is None:
                    path(m).unlink(missing_ok=True)
                    for base in [root/'.lake/build/lib/lean',root/'.lake/build/ir']:
                        stem=base/m.replace('.','/')
                        for p in stem.parent.glob(stem.name+'.*'):
                            if p.is_file():p.unlink()
                else:write_source(path(m),c['before'])
            build_all('restore-build',[m for m in plan['changes'] if path(m).exists()])
        report['sources_restored']=not success or not apply_changes
        save()
