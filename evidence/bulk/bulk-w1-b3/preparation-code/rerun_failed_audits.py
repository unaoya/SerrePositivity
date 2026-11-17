from pathlib import Path
import json,subprocess,os,hashlib,datetime,time
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout')
from check_frozen_main import check
check();summary=json.load(open(W/'all-audits-results.json'));results=summary['results'];assert len(results)==106
failures=[x for x in results if x['rc']!=0 or x['reason'] is not None];assert {x['path'] for x in failures}=={'scripts/audit_einfinity.lean'},failures
watcher=subprocess.Popen(['python3','-B',str(W/'live_budget_watch.py'),'--root-pid',str(os.getpid()),'--output','audit-rerun-aggregate-budget.json']);idle=subprocess.Popen(['caffeinate','-i','-w',str(os.getpid())]);reruns=[]
for row in failures:
 check();path=row['path'];log=W/'audit-einfinity-corrected-rerun.log';source_sha=hashlib.sha256((R/path).read_bytes()).hexdigest();p=subprocess.run(['python3','-B',str(W/'guard.py'),'--cwd',str(R),'--log',str(log),'--seconds','7200','--jobs','1','--threads','1','--','env','LEAN_NUM_THREADS=1','lake','env','lean',path]);record={'path':path,**json.load(open(str(log)+'.json')),'source_sha256':source_sha,'replaces_initial_failure':'audit-first-pass-failures/046.log'};reruns.append(record);(W/'audit-corrected-reruns.json').write_text(json.dumps(reruns,indent=2));assert record['rc']==0 and record['reason'] is None,record
 results=[record if old['path']==path else old for old in results]
assert len({x['path'] for x in results})==106 and all(x['rc']==0 and x['reason'] is None for x in results)
summary={'audits':106,'success':106,'failed':[],'results':results,'scheduling':'strictly serial; first-night 32 byte-identical input receipts retained; failed EInfinity required-name data corrected and whole audit rerun','initial_failures':'audit-first-pass-failures/failures.json','corrected_reruns':'audit-corrected-reruns.json','finished':time.time()}
for name in ['all-audits-results.json','all-audits-complete.json']:(W/name).write_text(json.dumps(summary,indent=2))
(W/'all-audits-progress.json').write_text(json.dumps(results,indent=2))
cp=json.load(open(W/'verified-source-checkpoint.json'));cp['audit_correction_pending_formal_rerun']=False;cp['audit_correction_passed_rerun']='audit-corrected-reruns.json';(W/'verified-source-checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2));print('Every formal audit PASS; correction full audit rerun succeeded',flush=True)
