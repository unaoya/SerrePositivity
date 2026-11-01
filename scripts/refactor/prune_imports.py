"""Minimize split files or one existing module; preserve declarations and build downstream."""
import json
from pathlib import Path
import re
import subprocess
import signal
import tempfile
import time

import layer_check as lc
from lean_source import read_source, write_source, parse_source, owner, declaration_owner
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


def reachable(graph, seeds):
    found=set(); todo=list(seeds)
    while todo:
        m=todo.pop()
        if m in found: continue
        found.add(m); todo.extend(graph.get(m, ()))
    return found


def missing_direct_imports(graph, module, snapshot):
    """Actual project constant dependencies lost through a pruned public import."""
    rows=snapshot['declarations']
    if any('used_modules' not in r for r in rows):
        raise ValueError('downstream snapshot requires used_modules')
    required={d for r in rows for d in r['used_modules'] if d != module}
    visible=reachable(graph,graph.get(module,()))
    missing=required-visible
    # Prefer defining project modules, which also bring their external dependencies.
    candidates={d for d in missing if lc.under(d,'SerrePositivity')}
    if not candidates: candidates=missing
    for dep in sorted(candidates):
        if module in reachable(graph,[dep]): raise ValueError('downstream repair would create a cycle: '+module)
    needed=set(candidates)
    for dep in sorted(candidates):
        if needed <= reachable(graph,candidates-{dep}): candidates.remove(dep)
    return candidates


def failed_modules(output):
    return sorted({m.replace('/','.') for m in re.findall(
        r"(?m)^error: (SerrePositivity(?:/[\w'-]+)+)\.lean:\d+:",output)})


def prune_plan(root, plan, snapshot, apply_changes=False):
    """Temporarily elaborate the plan even in dry-run; always restore on failure."""
    config=json.loads((root/'scripts/refactor/layers.json').read_text())
    graph,_=lc.read_graph(root,config)
    modules=list(plan['prune_modules']) if 'prune_modules' in plan else [plan['module'],plan['dest']]
    if plan.get('dependencies',{}).get('keep_to_moved'): modules.reverse()
    affected=affected_modules(graph,set(modules))
    directory=Path(tempfile.mkdtemp(prefix='prune-',dir=root/'.lake/verify'))
    records=[]
    report={'directory':str(directory),'commands':records,'modules':{},'affected_modules':affected,
            'preservation_checks':[], 'downstream_imports':{}, 'status':'RUNNING'}
    def path(m):return root/(m.replace('.','/')+'.lean')
    def save(): (directory/'results.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    def run(label,args,expected_failure=False,stop_on_error=False):
        start=time.monotonic();log=directory/(str(len(records))+'-'+label+'.log')
        report['active']=label;save()
        with log.open('w') as output:
            if stop_on_error:
                proc=subprocess.Popen(args,cwd=root,stdout=output,stderr=subprocess.STDOUT)
                # Search the entire log, not its tail; stop Lake once a module fails.
                interrupted=False
                while proc.poll() is None:
                    time.sleep(0.5)
                    if not interrupted and re.search(r'(?m)^error:',log.read_text()):
                        proc.send_signal(signal.SIGINT); interrupted=True
                rc=proc.wait()
            else:
                rc=subprocess.call(args,cwd=root,stdout=output,stderr=subprocess.STDOUT)
        report.pop('active',None)
        records.append({'label':label,'command':args,'exit_code':rc,'seconds':round(time.monotonic()-start,3),'log':str(log)})
        save()
        if rc and not expected_failure:raise RuntimeError('prune build failed: '+str(log))
        return rc,log.read_text()
    def build_all(label,targets,repair=False):
        # Build maximal affected targets; their dependency closure covers the rest.
        selected=set(targets)
        imported=set().union(*(graph.get(m,set()) & selected for m in selected))
        tips=sorted(selected-imported)
        if not tips:tips=sorted(selected)
        for i in range(0,len(tips),100):
            attempt=0
            while True:
                rc,output=run(label+'-'+str(i//100)+'-try'+str(attempt),
                    ['lake','build',*tips[i:i+100]],expected_failure=repair,stop_on_error=repair)
                if rc==0: break
                failures=failed_modules(output)
                if not failures: raise RuntimeError('non-module downstream failure; see '+str(directory))
                for failed in failures: repair_downstream(failed,output)
                attempt+=1
    def repair_downstream(module,output):
        if module in modules: raise RuntimeError('pruned module failed downstream: '+module)
        # Recover a trustworthy snapshot from original sources, including public reexports.
        changed={m:read_source(path(m)) for m in plan['changes']}
        before_file=directory/('downstream-'+module+'-before.json')
        try:
            for m,c in plan['changes'].items():
                if c['before'] is None: path(m).unlink(missing_ok=True)
                else: write_source(path(m),c['before'])
            run('downstream-original-build',['lake','build',module])
            run('downstream-original-snapshot',['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                '--modules',module,'--output',str(before_file)])
        finally:
            for m,text in changed.items(): write_source(path(m),text)
        baseline=json.loads(before_file.read_text())
        from split_module import downstream_repair_snapshot
        repair_snapshot=downstream_repair_snapshot(module,baseline,plan,snapshot,output,config)
        # Only this plan's temporary sources differ from the captured graph.
        current={m:set(ds) for m,ds in graph.items()}
        for m in plan['changes']: current[m]=lc.imports(read_source(path(m)))
        additions=missing_direct_imports(current,module,repair_snapshot)
        if not additions: raise RuntimeError('no missing constant dependency to repair: '+module)
        from split_module import add_import
        original=read_source(path(module)); updated=original
        for dep in sorted(additions): updated=add_import(updated,dep)
        if module not in plan['changes']:
            plan['changes'][module]={'before':original,'after':updated}
        else: plan['changes'][module]['after']=updated
        write_source(path(module),updated)
        report['downstream_imports'][module]=sorted(set(report['downstream_imports'].get(module,[]))|additions)
        plan['downstream_imports']=report['downstream_imports']; save()
        run('downstream-repaired-build',['lake','build',module])
        after_file=directory/('downstream-'+module+'-after.json')
        run('downstream-repaired-snapshot',['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
            '--modules',module,'--output',str(after_file)])
        result=compare(baseline,json.loads(after_file.read_text()))
        report['preservation_checks'].append({'module':module,'label':'downstream-repair','result':result,
            'before_snapshot':str(before_file),'snapshot':str(after_file)})
        save()
        if result['status']!='PASS': raise RuntimeError('downstream repair changes declarations: '+module)

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
                if plan['declaration_modules'].get(declaration_owner(r,plan['declaration_modules'],
                    {x['name']:x for x in snapshot['declarations']}))==m]}
            def preserved(label):
                run(label+'-build',['lake','build',m])
                target=directory/(str(len(records))+'-snapshot.json')
                run(label+'-snapshot',['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                    '--modules',m,'--output',str(target)])
                result=compare(baseline,json.loads(target.read_text()),module_map={'modules':{plan['module']:m}})
                report['preservation_checks'].append({'module':m,'label':label,'result':result,
                                                      'snapshot':str(target)})
                save()
                return result
            # Split source positions differ from the original snapshot. Capture
            # the built split module before pruning for anonymous-command lookup.
            positions_file=directory/(str(len(records))+'-positions.json')
            run('source-positions',['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                '--modules',m,'--output',str(positions_file)])
            position_snapshot=json.loads(positions_file.read_text())
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
            original_text=text
            removed_opens=[]
            candidate_fallback=False
            if rc:
                unavailable=set(re.findall(r'unknown namespace `([^`]+)`',output))
                parsed=parse_source(text, snapshot=position_snapshot, module=m)
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
                if removed_opens:
                    candidate=replace_imports(text,candidates);write_source(path(m),candidate)
                    rc,_=run('candidate-without-unused-open',['lake','env','lean',str(path(m))],True)
                if rc:
                    # minImports is a proposal, not a proof of elaboration equivalence.
                    # Start the checked removal loop from the known compiling source
                    # when that proposal underestimates required imports.
                    text=original_text; candidates=set(before); removed_opens=[]
                    candidate=text; write_source(path(m),candidate)
                    run('candidate-original-imports',['lake','env','lean',str(path(m))])
                    candidate_fallback=True
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
            report['modules'][m]={'before':before,'after':sorted(candidates),'removed_unused_opens':removed_opens,
                                  'min_imports_fallback':candidate_fallback}
            run('pruned-build',['lake','build',m])
        build_all('downstream-build',affected,repair=True)
        plan['downstream_imports']=report['downstream_imports']
        success=True;report['status']='PASS';save()
        plan['pruning']=report
        return plan
    except BaseException as exc:
        report['status']='FAIL';report['error']=str(exc);save()
        raise
    finally:
        try:
            if not success or not apply_changes:
                for m,c in plan['changes'].items():
                    if c['before'] is None:
                        path(m).unlink(missing_ok=True)
                        for base in [root/'.lake/build/lib/lean',root/'.lake/build/ir']:
                            stem=base/m.replace('.','/')
                            for p in stem.parent.glob(stem.name+'.*'):
                                if p.is_file():p.unlink()
                    else:write_source(path(m),c['before'])
                report['sources_restored']=True;save()
                build_all('restore-build',[m for m in plan['changes'] if path(m).exists()])
            else: report['sources_restored']=False
        except BaseException as exc:
            report['status']='FAIL';report['restore_error']=str(exc)
            raise
        finally: save()


def single_module_plan(root, module, snapshot):
    """Prune in place without pretending that a move or split has occurred."""
    source = read_source(root / (module.replace('.', '/') + '.lean'))
    saved = {row['module']: row['source'] for row in snapshot.get('sources', [])}
    if saved.get(module) != source:
        raise ValueError('snapshot source does not match: ' + module)
    if any(row['module'] != module for row in snapshot['declarations']):
        raise ValueError('single-module snapshot includes another module')
    return {'module': module, 'prune_modules': [module],
            'declaration_modules': {r['name']: module for r in snapshot['declarations']},
            'changes': {module: {'before': source, 'after': source}}}


def main():
    import argparse
    from split_module import ROOT, obtain_snapshot
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module')
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--apply', action='store_true', help='keep pruned source on success; otherwise restore')
    args = parser.parse_args()
    root = args.root.resolve()
    snapshot = json.loads(args.snapshot.read_text()) if args.snapshot else obtain_snapshot(root, args.module)
    plan = single_module_plan(root, args.module, snapshot)
    plan = prune_plan(root, plan, snapshot, apply_changes=args.apply)
    args.output.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
    print('PASS: ' + plan['pruning']['directory'])


if __name__ == '__main__': main()
