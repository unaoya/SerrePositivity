from pathlib import Path
import json,subprocess,time
w=Path('/tmp/bulk-w1-b3');b=w/'before';ms=json.load(open(w/'original-private-names.json'))['missing_modules'];ms=sorted(set(ms)|{'SerrePositivity.Util.Citation'});out=w/'before-comparison-prerequisites';out.mkdir(exist_ok=True)
for i in range(0,len(ms),48):
 for attempt in range(20):
  log=out/f'{i//48:03}-{attempt:02}.log'
  p=subprocess.run(['python3','-B',str(w/'guard.py'),'--cwd',str(b),'--log',str(log),'--night-only','--seconds','1500','--','lake','--fail-fast','build',*ms[i:i+48]],stdout=subprocess.DEVNULL)
  rec=json.load(open(str(log)+'.json'));print('before comparison prerequisites',i//48,p.returncode,flush=True)
  if p.returncode==75 and rec['reason']=='bounded batch':continue
  if p.returncode:raise SystemExit(p.returncode)
  break
 else:raise SystemExit('Too many bounded batches; inspect resource log')
p=subprocess.run(['python3','-B',str(w/'prepare_original_private.py')]);p.check_returncode()
assert not json.load(open(w/'original-private-names.json'))['missing_modules']
(w/'before-comparison-prerequisites-complete.json').write_text(json.dumps({'extra_modules':len(ms),'finished':time.time()}))
