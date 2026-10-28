#!/usr/bin/env python3
"""R72 の実ファイルで分割・ビルド・保存比較を試し、必ず元に戻す。"""
import json
from pathlib import Path
import subprocess
import sys
import time

from split_module import ROOT, module_path
import layer_check as lc

OUT=ROOT/'.lake/verify/ifw0-2-prune-test'
MODULE='SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions'
DEST='SerrePositivity.InfinityCategories.ModelBridge.IFW0FixedBoundaryModel'
PREFIX='SerrePositivity.SimplicialModel.RelativeChoiceSpace.'
MOVED=[PREFIX+n for n in ['restriction_trivialFibration','projection_trivialFibration','kanComplex',
                          'extension','interval','relative_homotopy','nonempty_fixedBoundaryHomotopy']]


def model_counts():
    config=json.loads((ROOT/'scripts/refactor/layers.json').read_text())
    graph,mentions=lc.read_graph(ROOT,config)
    nodes,index,masks=lc.closure_masks(graph)
    prefixes=[p for p in config['forbidden']['W2a_additions'] if p.startswith('SerrePositivity.HomotopicalAlgebra.') or p.endswith('.ModelBridge')]
    models={n for n in nodes if n in mentions or any(lc.under(n,p) for p in prefixes)}
    result={}
    for layer in ['HomotopyLimits','F1','F2']:
        roots=[n for n in graph if lc.classify(n,config)==layer]
        by_root={n:sorted(set(lc.selected_names(masks[n],nodes)) & models) for n in roots}
        result[layer]={'union_count':len(set().union(*map(set,by_root.values()))),
                       'closure_pairs':sum(map(len,by_root.values())),'by_module':by_root}
    return result


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    destination=module_path(ROOT,DEST)
    if destination.exists(): raise RuntimeError('temporary destination already exists')
    parent_existed=destination.parent.exists()
    state={'status':'running','started_epoch':time.time(),'commands':[]}
    plan=None;restored=False
    def save(): (OUT/'results.json').write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n')
    def run(label,args):
        state['active']=label;save();start=time.monotonic()
        with (OUT/(label+'.log')).open('w') as log:
            rc=subprocess.call(args,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
        row={'label':label,'command':args,'exit_code':rc,'seconds':round(time.monotonic()-start,3)}
        state['commands'].append(row);save();print(json.dumps(row),flush=True)
        if rc: raise RuntimeError('unexpected failure in '+label+'; see '+str(OUT/(label+'.log')))
    def snapshot(label,modules):
        run(label,['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean',
                   '--modules',','.join(modules),'--output',str(OUT/(label+'.json'))])
    try:
        state['model_before']=model_counts();save()
        run('before-build',['lake','build',MODULE])
        snapshot('before',[MODULE])
        common=[sys.executable,'scripts/refactor/split_module.py',MODULE,DEST,'--moved',*MOVED,
                '--snapshot',str(OUT/'before.json'),'--output',str(OUT/'plan.json')]
        run('dry-run',[*common,'--dry-run'])
        plan=json.loads((OUT/'plan.json').read_text())
        assert len(plan['moved'])==7 and len(plan['keep'])==16
        assert plan['dependencies']['moved_to_keep'] and not plan['dependencies']['keep_to_moved']
        assert all(n.startswith('SerrePositivity.') for n in plan['changes'])
        (OUT/'new-module.txt').write_text(plan['changes'][DEST]['after'])
        state['changed_modules']=list(plan['changes']);save()
        run('apply',[*common,'--apply','--prune-imports'])
        plan=json.loads((OUT/'plan.json').read_text())
        state['pruning_directory']=plan['pruning']['directory']
        assert 'SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility' not in lc.imports(plan['changes'][MODULE]['after'])
        (OUT/'new-module.txt').write_text(plan['changes'][DEST]['after'])
        (OUT/'retained-module.txt').write_text(plan['changes'][MODULE]['after'])
        state['model_after']=model_counts();save()
        run('split-build',['lake','build',*plan['changes']])
        snapshot('after',[MODULE,DEST])
        run('compare',[sys.executable,'scripts/refactor/compare_snapshots.py',str(OUT/'before.json'),
                       str(OUT/'after.json'),'--output',str(OUT/'comparison.json')])
        state['comparison']=json.loads((OUT/'comparison.json').read_text())
        state['status']='passed'
    except BaseException as exc:
        state['status']='failed';state['error']=str(exc);raise
    finally:
        if plan is not None:
            for mod,change in plan['changes'].items():
                path=module_path(ROOT,mod)
                if change['before'] is None:path.unlink(missing_ok=True)
                else:path.write_bytes(change['before'].encode('utf-8'))
            restored=all((not module_path(ROOT,n).exists()) if c['before'] is None else
                         module_path(ROOT,n).read_bytes()==c['before'].encode('utf-8') for n,c in plan['changes'].items())
            for base in [ROOT/'.lake/build/lib/lean',ROOT/'.lake/build/ir']:
                stem=base/DEST.replace('.','/')
                for p in stem.parent.glob(stem.name+'.*'):
                    if p.is_file():p.unlink()
            if not parent_existed and destination.parent.exists():destination.parent.rmdir()
        state['sources_restored']=restored
        try:
            if plan is not None and restored:
                # Restored sources invalidate downstream Lake traces automatically.
                # Rebuild the changed modules here; the later gate rebuilds its
                # root/audit closure. Rebuilding all unchanged downstream twice
                # is unnecessary for the split's preservation test.
                targets=[n for n in plan['changes'] if n!=DEST]
                run('restored-build',['lake','build',*targets])
        except BaseException as exc:
            state['status']='failed';state['restore_build_error']=str(exc);raise
        finally:
            state.pop('active',None);state['finished_epoch']=time.time();save()
            print('FINISHED',state['status'],'sources_restored=',restored,flush=True)


if __name__=='__main__':main()
