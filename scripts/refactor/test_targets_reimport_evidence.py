#!/usr/bin/env python3
"""IF-W0-3 §10.8: entry reimports + R59 check relocation, restored after verification."""
import argparse,json,re,subprocess,sys,time
from pathlib import Path
import layer_check as lc
from prune_imports import replace_imports
from split_module import ROOT,module_path

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--plan',type=Path,required=True);parser.add_argument('--output-dir',type=Path,required=True);args=parser.parse_args()
 out=args.output_dir;out.mkdir(parents=True,exist_ok=False)
 entries=[e for e in json.loads(args.plan.read_text()) if e['action']=='reimport']
 expected={'SerrePositivity',lc.IC+'.Stable',lc.IC+'.F2'}
 assert {e['module'] for e in entries}==expected,'only approved entrance modules may be trialled'
 original={e['module']:module_path(ROOT,e['module']).read_bytes() for e in entries}
 state={'status':'running','commands':[],'started_epoch':time.time(),'sources_restored':False,'preservation':'entry modules exempt under section 10.8-4'}
 def save():(out/'results.json').write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n')
 def run(label,cmd):
  state['active']=label;save();t=time.monotonic()
  with (out/(label+'.log')).open('w') as f:rc=subprocess.call(cmd,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT)
  state['commands'].append(dict(label=label,command=cmd,exit_code=rc,seconds=time.monotonic()-t));save()
  if rc:raise RuntimeError(label+' failed')
 try:
  for e in entries:
   m=e['module'];text=original[m].decode();checks=re.findall(r'(?m)^#check[^\n]*\n?',text)
   if checks:
    assert m==lc.IC+'.F2','unexpected checks outside F2'
    assert len(checks)==1497,('R59 check count mismatch',len(checks))
    checkfile=out/'R59Checks.lean'
    checkfile.write_text(''.join('import '+d+'\n' for d in sorted(lc.imports(text)))+'\n'+''.join(checks))
    text=re.sub(r'(?m)^#check[^\n]*\n?','',text);state['relocated_checks']=len(checks);state['temporary_audit']=str(checkfile)
   assert not re.search(r'(?m)^\s*(?:public\s+)?(?:def|theorem|lemma|instance|abbrev|axiom)\b',lc.code_only(text)), 'entry contains declarations'
   module_path(ROOT,m).write_text(replace_imports(text,e['imports'][m]))
  run('build',['lake','build',*sorted(expected)])
  run('relocated-checks',['lake','env','lean',str(checkfile)])
  run('layers',[sys.executable,'-B','scripts/refactor/layer_check.py','--report'])
  (out/'layers.json').write_bytes((ROOT/'.lake/verify/layers.json').read_bytes())
  state['status']='PASS'
 except BaseException as exc:state.update(status='FAIL',error=str(exc));raise
 finally:
  for m,data in original.items():module_path(ROOT,m).write_bytes(data)
  state['sources_restored']=all(module_path(ROOT,m).read_bytes()==data for m,data in original.items())
  state.pop('active',None);state['finished_epoch']=time.time();save()

if __name__=='__main__':main()
