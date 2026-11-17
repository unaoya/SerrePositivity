from pathlib import Path
import json,subprocess,time,hashlib,datetime
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');
if not (w/'before-comparison-prerequisites-complete.json').exists():subprocess.run(['python3','-B',str(w/'build_before_missing.py')],check=True)
plan=json.load(open(w/'target-build-plan.json'));out=w/'target-build';out.mkdir(exist_ok=True);failed=[]
def source_signature():
 return hashlib.sha256(json.dumps({m:hashlib.sha256((r/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in plan['modules']},sort_keys=True).encode()).hexdigest()
sig=source_signature()
for i,modules in enumerate(plan['groups']):
 record=out/f'{i:03}.json'
 if record.exists():
  old=json.load(open(record))
  if old.get('rc')==0 and old.get('source_signature')==sig and old.get('modules')==modules:continue
 attempt=0
 while True:
  if 8<=datetime.datetime.now().hour<23:raise SystemExit('Night target build paused at daytime boundary')
  log=out/f'{i:03}-{attempt:02}.log';cmd=['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(log),'--night-only','--seconds','1500','--','lake','--fail-fast','build',*modules]
  result=subprocess.run(cmd,stdout=subprocess.DEVNULL);resource=json.load(open(str(log)+'.json'));rec={'rc':result.returncode,'modules':modules,'source_signature':sig,'resource':resource};record.write_text(json.dumps(rec,indent=2))
  print('target group',i+1,'/',len(plan['groups']),'rc',result.returncode,'seconds',round(resource['seconds'],1),flush=True)
  if result.returncode==75 and resource['reason']=='bounded batch':attempt+=1;continue
  if result.returncode:failed.append({'group':i,'log':str(log),'rc':result.returncode})
  break
assert source_signature()==sig,'Target sources changed while building; rerun with fresh source signatures'
(w/'target-build-results.json').write_text(json.dumps({'groups':len(plan['groups']),'modules':len(plan['modules']),'failures':failed,'completed':time.time()},indent=2))
if failed:raise SystemExit(1)
(w/'target-build-complete.json').write_text(json.dumps({'modules':len(plan['modules']),'requested':plan['requested'],'finished':time.time(),'source_signature':sig},indent=2))

subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(w/'moved-audits-build.log'),'--night-only','--seconds','1500','--','python3','-B',str(w/'build_moved_audits.py')],check=True)
assert (w/'moved-audits-complete.json').exists()
subprocess.run(['python3','-B',str(w/'prepare_owned_private_rules.py')],check=True)

for script,marker in [('check_native_tag_metadata.py','native-tag-metadata-check.json'),('check_attribute_metadata.py','attribute-metadata-check.json'),('check_bulk_aliases.py','alias-check-complete.json')]:
 while not (w/marker).exists():
  subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(r),'--log',str(w/(script+'.log')),'--night-only','--seconds','1780','--','python3','-B',str(w/script)],check=True)
subprocess.run(['python3','-B',str(w/'preserve_driver.py')],check=True)

subprocess.run(['python3','-B',str(w/'night_gates.py')],check=True)
