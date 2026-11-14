from pathlib import Path
import json,sys,subprocess,hashlib,time,datetime,os
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');assert (W/'root-build-complete.json').exists();assert (W/'actual-preservation/complete.json').exists();sys.path.insert(0,str(R/'scripts/refactor'));from audit_imports import audit_build_targets
paths=sorted({p.relative_to(R).as_posix() for p in (R/'scripts').glob('audit_*.lean')}|{p.relative_to(R).as_posix() for p in (R/'scripts/audit').rglob('*.lean')});registered={s.strip() for s in (R/'scripts/refactor/audit_manifest.txt').read_text().splitlines() if s.strip() and not s.startswith('#')};assert set(paths)==registered,{'missing':sorted(registered-set(paths)),'unregistered':sorted(set(paths)-registered)};targets=sorted(audit_build_targets((R/p).read_text() for p in paths));(W/'all-audit-inventory.json').write_text(json.dumps({'count':len(paths),'audits':paths,'build_targets':targets,'policy':'Every scripts/audit_*.lean and scripts/audit/**/*.lean, exact manifest equality, no audit selected out'},indent=2));out=W/'all-audits';out.mkdir(exist_ok=True)
def lease(label,cmd,jobs,threads):
 now=datetime.datetime.now();assert now.hour>=23 or now.hour<8,'formal audits are night-only';budget=1650
 if now.hour<8:budget=min(budget,int((now.replace(hour=8,minute=0,second=0,microsecond=0)-now).total_seconds())-20)
 if budget<60:raise SystemExit(75)
 log=out/(label+'.log');command=['zsh',str(R/'scripts/refactor/with_build_lock.sh'),'--wait','3600','--class','bulk','--','python3',str(W/'guard.py'),'--cwd',str(R),'--log',str(log),'--night-only','--seconds',str(budget),'--jobs',str(jobs),'--threads',str(threads),'--',*cmd]
 with (out/(label+'.lease.log')).open('w') as f:p=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
 if not log.with_suffix('.log.json').exists():raise SystemExit(p.returncode)
 result=json.loads(log.with_suffix('.log.json').read_text());assert p.returncode==0 and result['rc']==0 and result['reason'] is None,(label,result);return result
if not (W/'all-audit-prerequisites-complete.json').exists():
 record=lease('prerequisites',['lake','build',*targets],8,3);(W/'all-audit-prerequisites-complete.json').write_text(json.dumps(record,indent=2));print('formal audit prerequisites PASS',flush=True)
application=json.loads((W/'actual-application.json').read_text());source_signature=hashlib.sha256(json.dumps(application['paths_written'],sort_keys=True).encode()).hexdigest()
def check_inputs():
 for path,sha in application['paths_written'].items():assert hashlib.sha256((R/path).read_bytes()).hexdigest()==sha,('source changed after application',path)
results=[]
for i,path in enumerate(paths):
 check_inputs()
 sha=hashlib.sha256((R/path).read_bytes()).hexdigest();receipt=out/f'{i:03}.json'
 if receipt.exists():
  old=json.loads(receipt.read_text())
  if old['source_sha256']==sha and old.get('source_signature')==source_signature and old['rc']==0 and old['reason'] is None:results.append(old);continue
 record={'path':path,'source_sha256':sha,'source_signature':source_signature,**lease(f'{i:03}',['lake','env','lean',path],1,1)};receipt.write_text(json.dumps(record,indent=2));results.append(record);(W/'all-audits-progress.json').write_text(json.dumps(results,indent=2));print('formal audit',i+1,len(paths),path,'PASS',round(record['seconds'],1),flush=True)
summary={'count':len(paths),'success':len(results),'failed':[],'results':results,'strictly_serial':True,'one_shared_ticket_per_audit':True,'source_signature':source_signature,'time':time.time()};assert len(results)==len(paths) and all(r['rc']==0 and r['reason'] is None for r in results);(W/'all-audits-complete.json').write_text(json.dumps(summary,indent=2));print('ALL FORMAL AUDITS PASS',flush=True)
