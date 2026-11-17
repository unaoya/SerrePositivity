from pathlib import Path
import json,subprocess,time,os,sys,hashlib,shutil
W=Path('/tmp/bulk-b3prime');A=Path('/tmp/bulk-b3prime-preview');budget=int(sys.argv[1]);start=time.monotonic();manifest=json.loads((W/'final-bundle/manifest.json').read_text());import_only={r['module'] for r in json.loads((W/'before-manifest.json').read_text())['import_only_modules']};mods=sorted(set(manifest['files'])-import_only);out=W/'target-build';out.mkdir(exist_ok=True)
for m,sha in manifest['files'].items():assert hashlib.sha256((A/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest()==sha,m
signature=hashlib.sha256(json.dumps(manifest['files'],sort_keys=True).encode()).hexdigest();groups=[mods[i:i+8] for i in range(0,len(mods),8)]
for i,group in enumerate(groups):
 done=out/f'{i:03}.json'
 if done.exists():
  previous=json.loads(done.read_text())
  if previous['signature']==signature:continue
  done.rename(done.with_name(done.stem+'.stale-'+previous['signature'][:12]+'.json'))
 left=int(budget-(time.monotonic()-start)-10)
 if left<40:raise SystemExit(75)
 t=time.monotonic();cmd=['lake','build',*group];log=out/f'{i:03}.log'
 if log.exists():shutil.copy2(log,log.with_name(log.stem+'.history-'+str(time.time_ns())+'.log'))
 with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(left),*cmd],cwd=A,env=dict(os.environ,LEAN_NUM_THREADS='3'),stdout=f,stderr=subprocess.STDOUT)
 receipt={'modules':group,'signature':signature,'command':cmd,'rc':r.returncode,'seconds':time.monotonic()-t,'log':str(log)};(out/f'{i:03}.attempt.json').write_text(json.dumps(receipt,indent=2));print(i,r.returncode,round(receipt['seconds'],2),flush=True)
 if r.returncode in [124,137]:raise SystemExit(75)
 if r.returncode:raise SystemExit(1)
 done.write_text(json.dumps(receipt,indent=2))
(out/'complete.json').write_text(json.dumps({'modules':len(mods),'groups':len(groups),'signature':signature,'finished':time.time()},indent=2));print('TARGET BUILD COMPLETE',flush=True)
