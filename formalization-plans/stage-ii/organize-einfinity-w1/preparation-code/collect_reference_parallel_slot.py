"""Resume original compiler reference capture in one bounded build-lock lease."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time,concurrent.futures,re
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--tools',type=Path,required=True);p.add_argument('--files',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--budget',type=int,default=265);p.add_argument('--stable-files',type=Path);a=p.parse_args();started=time.monotonic();root=a.root.resolve();tools=a.tools.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);caps=out/'captures';caps.mkdir(exist_ok=True)
sys.path.insert(0,str(tools));import bulk_collect as B;from klw1_namespace import checked_capture,module_name
helper_sha=hashlib.sha256(B.patched_helper((tools/'klw1_collect_refs.lean').read_text()).encode()).hexdigest();base=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();assert base=='30ae8948f339beec42d9340feb02f2031c22c72b';files=json.loads(a.files.read_text());fingerprint={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in files}
stable=json.loads(a.stable_files.read_text()) if a.stable_files else {}
assert all(f in fingerprint and fingerprint[f]==sha for f,sha in stable.items())
required=[f for f in files if f not in stable]
sig=hashlib.sha256(json.dumps(dict(base=base,helper_sha=helper_sha,sources=fingerprint,lakefile=hashlib.sha256((root/'lakefile.toml').read_bytes()).hexdigest(),manifest=hashlib.sha256((root/'lake-manifest.json').read_bytes()).hexdigest()),sort_keys=True).encode()).hexdigest()
def valid(path):
 m=module_name(path);r=caps/(m+'.receipt.json');d=caps/(m+'.json')
 if not r.exists() or not d.exists():return False
 x=json.loads(r.read_text());return x.get('signature')==sig and x.get('returncode')==0 and x.get('capture_sha256')==hashlib.sha256(d.read_bytes()).hexdigest()
# Import successful existing original captures only after validating bytes and configured frontend.
for path,directory in [('SerrePositivity/EInfinity/FrameHom/AnodyneWeakDetection.lean','0'),('SerrePositivity/EInfinity/FrameHom/AnodyneFamilyHomotopy.lean','1'),('SerrePositivity/EInfinity/SimplicialLocalization/ModelRightFrameComparison.lean','2')]:
 if path not in fingerprint or valid(path):continue
 m=module_name(path);seed=Path('/private/tmp/oe-w1-reference-probe')/directory/(m+'.json')
 if not seed.exists():continue
 data=checked_capture(root,path,seed);assert data['elaboration']['collector_sha256']==helper_sha;dest=caps/(m+'.json');dest.write_bytes(seed.read_bytes());(caps/(m+'.receipt.json')).write_text(json.dumps(dict(signature=sig,returncode=0,source=path,capture_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),seed=str(seed),helper_sha=helper_sha),indent=2)+'\n')
# Same read-only two-capture resource guard used by B3. Never parallelize lake builds.
def available_memory():
 try:
  raw=subprocess.check_output(['vm_stat'],text=True);size=int(re.search(r'page size of (\d+) bytes',raw)[1])
  return size*sum(int(re.search(r'Pages '+label+r':\s+(\d+)',raw)[1]) for label in ['free','inactive','speculative'])
 except (OSError,ValueError,TypeError,subprocess.SubprocessError):return 0
available=available_memory();workers=2 if available>=20*1024**3 else 1
os.environ['LEAN_NUM_THREADS']='1'
new=[];failure=None
pending=iter(f for f in required if not valid(f))
def capture(path):
 remaining=a.budget-(time.monotonic()-started)
 if remaining<80:return None
 m=module_name(path);limit=max(1,min(190,int(remaining-12)));begin=time.monotonic()
 with tempfile.TemporaryDirectory(prefix='oe-w1-refs-') as td:
  td=Path(td);(td/'files.json').write_text(json.dumps([path]));dest=td/'output'
  with (caps/(m+'.log')).open('w') as log:r=subprocess.run(['gtimeout','--kill-after=3s',str(limit),sys.executable,str(tools/'bulk_namespace.py'),'collect','--root',str(root),'--files',str(td/'files.json'),'--output',str(dest)],stdout=log,stderr=subprocess.STDOUT,cwd=root)
  if r.returncode:return dict(failed=True,file=path,returncode=r.returncode,seconds=time.monotonic()-begin,limit_seconds=limit)
  data=checked_capture(root,path,dest/(m+'.json'));assert data['elaboration']['collector_sha256']==helper_sha;target=caps/(m+'.json');target.write_bytes((dest/(m+'.json')).read_bytes());rec=dict(signature=sig,returncode=0,source=path,capture_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),source_sha256=fingerprint[path],seconds=time.monotonic()-begin,helper_sha=helper_sha,refs=len(data['refs']),commands=len(data['commands']));(caps/(m+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
 active={}
 def submit():
  if failure or a.budget-(time.monotonic()-started)<80:return
  path=next(pending,None)
  if path is not None:active[pool.submit(capture,path)]=path
 for _ in range(workers):submit()
 while active:
  done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in done:
   path=active.pop(future);rec=future.result()
   if rec and rec.get('failed'):
    failure=rec;(out/'last-error.json').write_text(json.dumps(failure,indent=2)+'\n');print('Capture incomplete',failure,flush=True)
   elif rec:
    new.append(rec);print('Captured',path,round(rec['seconds'],2),flush=True)
   submit()
completed=[f for f in required if valid(f)];(out/'completed-files.json').write_text(json.dumps(completed,indent=2)+'\n');summary=dict(signature=sig,base=base,completed_files=len(completed),total_files=len(required),unchanged_scope_files=len(stable),candidate_files=len(files),new_captures=new,failure=failure,workers=workers,available_memory_bytes=available,seconds=time.monotonic()-started,complete=len(completed)==len(required));(out/'progress.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
if not failure and (out/'pause-after-batch').exists() and not summary['complete']:
 print('Requested orchestration pause after successful capture and lease release',flush=True);raise SystemExit(76)
raise SystemExit(1 if failure else 0)
