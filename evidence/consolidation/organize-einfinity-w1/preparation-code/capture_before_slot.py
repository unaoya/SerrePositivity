"""Bounded raw native inventory of the immutable OE-W1 baseline; not a preservation verdict."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--modules',type=Path,required=True);p.add_argument('--snapshot',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--budget',type=int,default=265);args=p.parse_args()
started=time.monotonic();root=args.root.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True);(out/'captures').mkdir(exist_ok=True)
base=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();assert base=='30ae8948f339beec42d9340feb02f2031c22c72b'
modules=json.loads(args.modules.read_text());assert len(modules)==len(set(modules))==588
binary_sha=hashlib.sha256(args.snapshot.read_bytes()).hexdigest();sources={m:hashlib.sha256((root/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in modules}
sig=hashlib.sha256(json.dumps(dict(base=base,binary_sha=binary_sha,sources=sources,flags=['--stable-project'],schema='raw-before-oe-w1-v1'),sort_keys=True).encode()).hexdigest()
planpath=out/'plan.json'
if planpath.exists():
 plan=json.loads(planpath.read_text());assert plan['signature']==sig
else:
 plan=dict(signature=sig,base=base,binary_sha=binary_sha,groups=[dict(label=f'{i//8:04}',modules=modules[i:i+8]) for i in range(0,len(modules),8)])
 planpath.write_text(json.dumps(plan,indent=2)+'\n')
def valid(g):
 r=out/'captures'/(g['label']+'.receipt.json');d=out/'captures'/(g['label']+'.json')
 if not r.exists() or not d.exists():return False
 x=json.loads(r.read_text());return x.get('signature')==sig and x.get('returncode')==0 and x.get('capture_sha256')==hashlib.sha256(d.read_bytes()).hexdigest()
prefix=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip();env=dict(os.environ,LEAN_SYSROOT=prefix,LEAN_NUM_THREADS='1');splits=[];completed=[]
for g in list(plan['groups']):
 if valid(g):continue
 remaining=args.budget-(time.monotonic()-started)
 if remaining<110:break
 dest=out/'captures'/(g['label']+'.json');dest.unlink(missing_ok=True);log=dest.with_suffix('.log');limit=max(1,min(240,int(remaining-12)));begin=time.monotonic()
 with log.open('w') as f:
  r=subprocess.run(['gtimeout','--kill-after=3s',str(limit),'lake','env',str(args.snapshot),'--stable-project','--modules',','.join(g['modules']),'--output',str(dest)],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 rec=dict(signature=sig,label=g['label'],modules=g['modules'],returncode=r.returncode,seconds=time.monotonic()-begin,limit_seconds=limit,policy='raw before inventory only; final normalization/comparison pending')
 if r.returncode:
  dest.unlink(missing_ok=True)
  if r.returncode in [124,137] and len(g['modules'])>1:
   n=len(g['modules'])//2;i=plan['groups'].index(g);plan['groups'][i:i+1]=[dict(label=g['label']+'a',modules=g['modules'][:n]),dict(label=g['label']+'b',modules=g['modules'][n:])];splits.append(rec);planpath.write_text(json.dumps(plan,indent=2)+'\n');print('Split for a later lease',g['label'],flush=True)
  else:(out/'error.json').write_text(json.dumps(rec,indent=2)+'\n');raise SystemExit(r.returncode)
  break
 data=json.loads(dest.read_text());assert set(data['modules'])==set(g['modules']) and data['count']==len(data['declarations'])
 assert all(hashlib.sha256(s['source'].encode()).hexdigest()==sources[s['module']] for s in data['sources'])
 assert {s['module'] for s in data['sources']}==set(g['modules'])
 rec.update(capture_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),declarations=data['count'],huge_terms=len(data['huge_terms']));dest.with_suffix('.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');completed.append(rec);print('Captured',g['label'],len(g['modules']),data['count'],round(rec['seconds'],2),flush=True)
summary=dict(signature=sig,base=base,completed_modules=sum(len(g['modules']) for g in plan['groups'] if valid(g)),total_modules=len(modules),completed_groups=sum(valid(g) for g in plan['groups']),total_groups=len(plan['groups']),new_captures=completed,new_splits=splits,seconds=time.monotonic()-started,complete=all(valid(g) for g in plan['groups']),policy='Raw native source ownership inventory; no before/after preservation comparison yet')
(out/'progress.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
