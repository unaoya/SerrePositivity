#!/usr/bin/env python3
"""IF-W0-3 §10: 実ファイルの分割証拠を採り、成功・失敗時ともソースを復元する。"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time
from split_module import ROOT,module_path
import layer_check as lc

IC='SerrePositivity.InfinityCategories'
CASES={
'transport-algebra':(IC+'.F2.CatInfinity.FunctorIsoTransportAlgebra',IC+'.Core.FunctorIsoTransportAlgebra',
 [IC+'.F2.functorIso_postcomp_heq_of_heq']),
'chain-transport':(IC+'.F2.FilteredExchange.FunctorIsoChainTransport',IC+'.Core.FunctorIsoChainTransport',
 [IC+'.F2.functorIso_postcomp_heq_of_map_eq']),
'whisker-cancellation':(IC+'.F2.FilteredExchange.FunctorIsoWhiskerCancellation',IC+'.Core.FunctorIsoWhiskerCancellation',
 [IC+'.F2.'+n for n in ('functorIso_precomp_precomp','functorIso_precomp_heq_of_map_eq')]),
'core-trivial':(IC+'.F2.CatInfinity.CoreTrivialFibration',IC+'.F1.CoreTrivialFibration',
 [IC+'.F2.'+n for n in ('coreLiftOfFullyFaithful','coreMap_trivialKanFibration')]),
'space-limits':(IC+'.F2.FilteredExchange.SpaceLimitShapes',IC+'.F1B.SpaceLimitShapes',
 [IC+'.F2.'+n for n in ('HasSpaceLimitsOfShape','hasSpaceLimitsOfShape')]),
}

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('case',choices=CASES);parser.add_argument('--output-dir',type=Path,default=ROOT/'.lake/verify/ifw0-3-revision/splits');args=parser.parse_args()
 module,dest,moved=CASES[args.case]
 out=args.output_dir/args.case
 out.mkdir(parents=True,exist_ok=False)
 state={'case':args.case,'module':module,'dest':dest,'started_epoch':time.time(),'status':'running','commands':[]}
 plan=None
 def save(): (out/'results.json').write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n')
 def run(label,cmd):
  state['active']=label;save();start=time.monotonic()
  with (out/(label+'.log')).open('w') as log:rc=subprocess.call(cmd,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
  state['commands'].append(dict(label=label,command=cmd,exit_code=rc,seconds=round(time.monotonic()-start,3)));save()
  print(json.dumps(state['commands'][-1]),flush=True)
  if rc:raise RuntimeError('STOP: '+label+' exit '+str(rc)+'; '+str(out/(label+'.log')))
 def snap(label,mods):run(label,['lake','env','lean','--run','scripts/refactor/decl_snapshot.lean','--modules',','.join(mods),'--output',str(out/(label+'.json'))])
 try:
  if module_path(ROOT,dest).exists():raise RuntimeError('destination exists: '+dest)
  run('baseline-build',['lake','build',module]);snap('before',[module])
  common=[sys.executable,'-B','scripts/refactor/split_module.py',module,dest,'--moved',*moved,'--snapshot',str(out/'before.json'),'--output',str(out/'plan.json')]
  run('dry-run',[*common,'--dry-run']);plan=json.loads((out/'plan.json').read_text())
  (out/'unpruned-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
  run('apply-prune',[*common,'--apply','--prune-imports']);plan=json.loads((out/'plan.json').read_text())
  state['imports']={m:sorted(lc.imports(plan['changes'][m]['after'])) for m in (module,dest)}
  state['pruning_directory']=plan['pruning']['directory'];save()
  run('split-build',['lake','build',module,dest]);snap('after',[module,dest])
  run('compare',[sys.executable,'-B','scripts/refactor/compare_snapshots.py',str(out/'before.json'),str(out/'after.json'),'--output',str(out/'comparison.json')])
  for m,label in [(module,'retained'),(dest,'moved')]: (out/(label+'.txt')).write_text(module_path(ROOT,m).read_text())
  state['status']='PASS'
 except BaseException as exc:
  state['status']='FAIL';state['error']=str(exc);raise
 finally:
  if plan is not None:
   for m,c in plan['changes'].items():
    p=module_path(ROOT,m)
    if c['before'] is None:p.unlink(missing_ok=True)
    else:p.write_bytes(c['before'].encode())
   state['sources_restored']=all((not module_path(ROOT,m).exists()) if c['before'] is None else module_path(ROOT,m).read_bytes()==c['before'].encode() for m,c in plan['changes'].items())
   for base in [ROOT/'.lake/build/lib/lean',ROOT/'.lake/build/ir']:
    stem=base/dest.replace('.','/')
    for p in stem.parent.glob(stem.name+'.*'):
     if p.is_file():p.unlink()
   try:run('restore-build',['lake','build',*[m for m,c in plan['changes'].items() if c['before'] is not None]])
   except BaseException as exc:state['status']='FAIL';state['restore_error']=str(exc);raise
  else:state['sources_restored']=True
  state.pop('active',None);state['finished_epoch']=time.time();save()
  print('FINISHED',state['status'],'sources_restored',state['sources_restored'],flush=True)

if __name__=='__main__':main()
