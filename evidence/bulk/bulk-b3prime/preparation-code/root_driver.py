from pathlib import Path
import datetime,json,subprocess,hashlib,os
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');assert (W/'actual-application.json').exists();i=len(list(W.glob('root-build-[0-9][0-9][0-9].log.json')))
while not (W/'root-build-complete.json').exists():
 now=datetime.datetime.now();assert now.hour>=23 or now.hour<8,'root bulk is night-only';budget=min(1650,int((now.replace(hour=8,minute=0,second=0,microsecond=0)-now).total_seconds())-15) if now.hour<8 else 1650
 if budget<60:raise SystemExit(75)
 label=f'root-build-{i:03}';log=W/(label+'.log');driverlog=W/(label+'.lease.log');cmd=['zsh',str(R/'scripts/refactor/with_build_lock.sh'),'--wait','3600','--class','bulk','--','python3',str(W/'guard.py'),'--cwd',str(R),'--log',str(log),'--night-only','--seconds',str(budget),'--jobs','8','--threads','3','--','lake','build','SerrePositivity']
 with driverlog.open('w') as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
 print(label,r.returncode,flush=True)
 if r.returncode==0:
  record=json.loads(log.with_suffix('.log.json').read_text());record['application_receipt_sha256']=hashlib.sha256((W/'actual-application.json').read_bytes()).hexdigest();(W/'root-build-complete.json').write_text(json.dumps(record,indent=2));break
 if r.returncode!=75:raise SystemExit(r.returncode)
 i+=1
