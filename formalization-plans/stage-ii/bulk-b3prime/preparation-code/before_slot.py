from pathlib import Path
import json,sys,os,time,subprocess,hashlib,uuid
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');sys.path.insert(0,str(R/'scripts/refactor'));import bulk_collect
plan=json.loads((W/'before-manifest.json').read_text());start=time.monotonic();budget=int(sys.argv[1]);out=W/'before';out.mkdir(exist_ok=True);env=dict(os.environ,LEAN_NUM_THREADS='2');binary=Path('/tmp/bulk-w1-b2/private-snapshot/snapshot');binsha=hashlib.sha256(binary.read_bytes()).hexdigest()
# Own source worktree is the immutable mathematical baseline. Documents do not enter this assertion.
changed=subprocess.check_output(['git','diff','--name-only','32d364b53','--','SerrePositivity','SerrePositivity.lean','scripts','lakefile.toml','lean-toolchain'],cwd=R,text=True).strip();assert not changed,changed

def run(label,cmd):
 left=int(budget-(time.monotonic()-start)-10)
 if left<35:raise SystemExit(75)
 log=out/(label+'.log');t=time.monotonic()
 with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(left),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 receipt={'command':cmd,'rc':r.returncode,'seconds':time.monotonic()-t,'log':str(log),'limit':left};(out/(label+'.receipt.json')).write_text(json.dumps(receipt,indent=2));print(label,r.returncode,round(receipt['seconds'],2),flush=True)
 if r.returncode in [124,137]:raise SystemExit(75)
 if r.returncode:raise SystemExit(1)
if not (W/'r82-consumers-final.complete.json').exists():
 run('r82-consumers-final',['python3',str(W/'r82_consumers_slot.py')])
 (W/'r82-consumers-final.complete.json').write_text(json.dumps({'time':time.time(),'comparison':'r82-consumers-comparison.json'}))
for i,mods in enumerate(plan['groups']):
 label=f'group-{i:03}';snap=out/(label+'.json');done=out/(label+'.complete.json')
 if done.exists():
  receipt=json.loads(done.read_text());assert receipt['snapshot_binary_sha256']==binsha
  assert receipt['snapshot_sha256']==hashlib.sha256(snap.read_bytes()).hexdigest()
 else:
  run(label+'-build',['lake','build',*mods]);run(label+'-snapshot',['lake','env',str(binary),'--stable-project','--modules',','.join(mods),'--output',str(snap)])
  d=json.loads(snap.read_text());assert set(d['modules'])==set(mods);assert all((R/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in d['sources'])
  done.write_text(json.dumps({'modules':mods,'snapshot_sha256':hashlib.sha256(snap.read_bytes()).hexdigest(),'snapshot_binary_sha256':binsha,'count':len(d['declarations'])},indent=2))
 for m in mods:
  path=m.replace('.','/')+'.lean'
  if path not in plan['reference_files']:continue
  dest=out/('refs-'+m)
  if (dest/'files.json').exists():
   data=json.loads((dest/(m+'.json')).read_text());assert data['source']==(R/path).read_text();continue
  attempt=out/('attempt-'+m+'-'+uuid.uuid4().hex);files=out/('file-'+m+'.json');files.write_text(json.dumps([path]))
  run('refs-'+m,['python3',str(R/'scripts/refactor/bulk_collect.py'),'--root',str(R),'--files',str(files),'--output',str(attempt)])
  assert (attempt/'files.json').exists();attempt.rename(dest)
 if budget-(time.monotonic()-start)<40:raise SystemExit(75)
(out/'complete.json').write_text(json.dumps({'modules':len(plan['modules']),'semantic_files':len(plan['reference_files']),'finished':time.time()},indent=2));print('BEFORE COMPLETE',flush=True)
