"""Finite capture batches: one ticket at a time; release before preview/review."""
from pathlib import Path
import argparse,json,subprocess,sys,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--slots',type=int,default=40);a=p.parse_args();root=a.root.resolve();code=root/'formalization-plans/stage-ii/organize-einfinity-w1/preparation-code';out=Path('/private/tmp/oe-w1-refs-before');plan=root/'formalization-plans/stage-ii/organize-einfinity-w1/namespace-rewrite-map.json'
for slot in range(a.slots):
 progress=out/'progress.json'
 if progress.exists() and json.loads(progress.read_text()).get('complete'):print('Complete',flush=True);break
 stamp=str(time.time_ns());log=out/('batch-'+stamp+'.log')
 command=['zsh','scripts/refactor/with_build_lock.sh','--class','bulk','--wait','3600','--','gtimeout','--kill-after=5s','280s',sys.executable,str(code/'collect_reference_parallel_slot.py'),'--root','/private/tmp/oe-w1-before-30ae8948f','--tools',str(root/'scripts/refactor'),'--files','/private/tmp/oe-w1-reference-candidates/core-files.json','--stable-files','/private/tmp/oe-w1-reference-candidates/unchanged-scope-files.json','--output',str(out),'--budget','265']
 print('Queueing batch',slot+1,log,flush=True)
 with log.open('w') as f:r=subprocess.run(command,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 print('Released batch',slot+1,'returncode',r.returncode,flush=True)
 if r.returncode==75:
  print('Ticket wait timed out; requeueing at the back, with no second ticket outstanding',flush=True);continue
 if r.returncode:
  print('Stopped: unsuccessful batch; successful receipts remain resumable',flush=True);raise SystemExit(r.returncode)
 # Not holding the lease here. Do not apply a blocked preview.
 r=subprocess.run([sys.executable,str(code/'preview_completed.py'),'--root','/private/tmp/oe-w1-before-30ae8948f','--tools',str(root/'scripts/refactor'),'--captures',str(out/'captures'),'--plan',str(plan),'--output','/private/tmp/oe-w1-native-plan/completed-preview'],cwd=root)
 if r.returncode:print('Stopped for preview diagnostics',flush=True);raise SystemExit(r.returncode)
 if progress.exists():
  x=json.loads(progress.read_text());print('Captured',x['completed_files'],'/',x['total_files'],'stable',x.get('unchanged_scope_files'),flush=True)
