from pathlib import Path
import json,subprocess,time,hashlib,datetime
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');plan=json.load(open(w/'target-build-plan.json'));out=w/'target-build';out.mkdir(exist_ok=True);failed=[]
for i,modules in enumerate(plan['groups']):
 sig=hashlib.sha256(json.dumps({m:hashlib.sha256((r/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in plan['modules']},sort_keys=True).encode()).hexdigest()
 record=out/f'{i:03}.json'
 if record.exists():
  old=json.load(open(record))
  if old.get('rc')==0 and old.get('source_signature')==sig:continue
 attempt=0
 while True:
  if 8<=datetime.datetime.now().hour<23:raise SystemExit('Night target build paused at daytime boundary')
  log=out/f'{i:03}-{attempt:02}.log';cmd=['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(log),'--night-only','--seconds','1500','--','lake','--fail-fast','build',*modules]
  result=subprocess.run(cmd,stdout=subprocess.DEVNULL);resource=json.load(open(str(log)+'.json'));rec={'rc':result.returncode,'modules':modules,'source_signature':sig,'resource':resource};record.write_text(json.dumps(rec,indent=2))
  print('target group',i+1,'/',len(plan['groups']),'rc',result.returncode,'seconds',round(resource['seconds'],1),flush=True)
  if result.returncode==75 and resource['reason']=='bounded batch':attempt+=1;continue
  if result.returncode:failed.append({'group':i,'log':str(log),'rc':result.returncode})
  break
(w/'target-build-results.json').write_text(json.dumps({'groups':len(plan['groups']),'modules':len(plan['modules']),'failures':failed,'completed':time.time()},indent=2))
if failed:raise SystemExit(1)
(w/'target-build-complete.json').write_text(json.dumps({'modules':len(plan['modules']),'requested':plan['requested'],'finished':time.time(),'source_signature':sig},indent=2))
