"""Capture observed native owners and citation metadata; not a preservation verdict."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--modules',type=Path,required=True);p.add_argument('--binary',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();code=Path(__file__).resolve().parent;out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(a.binary.read_bytes())=='d2a3604b79e658af8a36d71484da0fd5989c58045902d81f8611aeeddfac4809'
assert sha((code.parents[3]/'scripts/refactor/oe_native_owners.lean').read_bytes())=='1684ee5be48907d358fff7f6c8376ad2d9f0ffe7cba4fa20b61c9406716e18b9'
modules=json.loads(a.modules.read_text());assert len(modules)==len(set(modules));sources={m:sha((root/(m.replace('.','/')+'.lean')).read_bytes()) for m in modules};prefix=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip();env=os.environ|{'LEAN_SYSROOT':prefix,'LEAN_NUM_THREADS':'1'};started=time.monotonic()
raw=subprocess.check_output(['vm_stat'],text=True);page=int(re.search(r'page size of (\d+) bytes',raw)[1]);available=page*sum(int(re.search(r'Pages '+label+r':\s+(\d+)',raw)[1]) for label in ['free','inactive','speculative']);workers=2 if available>=20*1024**3 else 1
commands=[('owners',['lake','env',str(a.binary.resolve()),str(a.modules.resolve()),str(out/'owners.json')]),('citations',['python3',str(code/'capture_citations.py'),'--root',str(root),'--modules',str(a.modules.resolve()),'--output',str(out/'citations'),'--seconds','235'])]
def run(item):
 label,cmd=item;begin=time.monotonic();limit=min(240,int(265-(begin-started))-10)
 if limit<40:return dict(label=label,returncode=75,reason='Insufficient time remaining; retry in another lease')
 if label=='citations':cmd=cmd[:-1]+[str(max(1,limit-12))]
 with (out/(label+'.log')).open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(limit)+'s',*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 record=dict(label=label,returncode=r.returncode,seconds=time.monotonic()-begin,command=cmd);print(json.dumps(record),flush=True);return record
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:results=list(pool.map(run,commands))
assert all(sha((root/(m.replace('.','/')+'.lean')).read_bytes())==digest for m,digest in sources.items())
receipt=dict(results=results,seconds=time.monotonic()-started,readers=workers,available_memory_bytes=available,root=str(root),source_sha256=sources,sysroot=prefix,modules_sha256=sha(a.modules.read_bytes()),policy='Actual native ownership and citation metadata only; independent v3b is still required');(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['seconds','readers','available_memory_bytes']}));raise SystemExit(0 if all(r['returncode']==0 for r in results) else 1)
