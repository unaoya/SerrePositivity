from pathlib import Path
import json,subprocess,os,concurrent.futures,shutil,time,threading
w=Path('/tmp/bulk-w1-b3');b=w/'before';files=json.load(open(w/'delta-files.json'));groups=[files[i:i+12] for i in range(0,len(files),12)];pending=[];errors=[];env=dict(os.environ,LEAN_NUM_THREADS='1')
for i,paths in enumerate(groups):
 dest=w/'delta-captures'/f'{i:03}';dest.mkdir(exist_ok=True);old=dest.with_name(dest.name+'-pending')
 if old.exists():
  for p in old.glob('*.json'):
   if p.name=='files.json':continue
   d=json.load(open(p));rel=d['module'].replace('.','/')+'.lean';assert d['source'].encode()==(b/rel).read_bytes();p.replace(dest/p.name)
 for rel in paths:
  p=dest/(rel[:-5].replace('/','.')+'.json')
  if p.exists():assert json.load(open(p))['source'].encode()==(b/rel).read_bytes()
  else:pending.append((i,rel))
 if all((dest/(rel[:-5].replace('/','.')+'.json')).exists() for rel in paths):
  (dest/'files.json').write_text(json.dumps(sorted(paths)))
def one(item):
 i,rel=item;dest=w/'delta-captures'/f'{i:03}';tmp=w/'single-captures'/rel[:-5].replace('/','.')
 if tmp.exists():shutil.rmtree(tmp)
 tmp.parent.mkdir(exist_ok=True);log=tmp.with_suffix('.log');start=time.monotonic()
 with log.open('w') as f:p=subprocess.run(['gtimeout','--kill-after=3s','900','python3','-B',str(w/'collect_one.py'),str(b),rel,str(tmp)],env=env,stdout=f,stderr=subprocess.STDOUT)
 if p.returncode:errors.append({'path':rel,'rc':p.returncode,'log':str(log)});print('collect failure',rel,p.returncode,flush=True);return
 capture=tmp/(rel[:-5].replace('/','.')+'.json');d=json.load(open(capture));assert d['source'].encode()==(b/rel).read_bytes();capture.replace(dest/capture.name)
 paths=groups[i]
 if all((dest/(x[:-5].replace('/','.')+'.json')).exists() for x in paths):
  part=dest/('files.'+str(threading.get_ident())+'.tmp');part.write_text(json.dumps(sorted(paths)));part.replace(dest/'files.json')
 print('collect',rel,round(time.monotonic()-start,2),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 for _ in pool.map(one,pending):pass
(w/'collect-errors.json').write_text(json.dumps(errors,indent=2))
if errors:raise SystemExit(1)
assert sum(len(json.load(open(w/'delta-captures'/f'{i:03}'/'files.json'))) for i in range(len(groups)))==686
(w/'delta-collect-complete.json').write_text(json.dumps({'files':686,'errors':0,'completed':time.time(),'separate_worker_processes':True,'maxHeartbeats_resource_override':0},indent=2))
