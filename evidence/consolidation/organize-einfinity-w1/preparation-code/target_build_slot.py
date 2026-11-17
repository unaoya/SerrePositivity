"""Run a bounded, resumable target build in dependency order inside one bulk lease."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--modules',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--budget',type=int,required=True);a=p.parse_args();root=a.root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);start=time.monotonic();mods=json.loads(a.modules.read_text());assert len(mods)==len(set(mods));sha=lambda b:hashlib.sha256(b).hexdigest();sources={m:sha((root/(m.replace('.','/')+'.lean')).read_bytes()) for m in mods};signature=sha(json.dumps(dict(sources=sources,order=mods),sort_keys=True).encode());groups=[mods[i:i+8] for i in range(0,len(mods),8)]
for i,group in enumerate(groups):
 done=out/f'{i:04}.json'
 if done.exists() and json.loads(done.read_text())['signature']==signature:continue
 left=int(a.budget-(time.monotonic()-start)-10)
 if left<40:raise SystemExit(75)
 t=time.monotonic();cmd=['lake','build',*group];log=out/f'{i:04}.log'
 if log.exists():shutil.copy2(log,log.with_name(log.stem+'.history-'+str(time.time_ns())+'.log'))
 # The outer B3 process guard also terminates descendants on the lease deadline.
 with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(left),*cmd],cwd=root,env=os.environ|{'LEAN_NUM_THREADS':'3'},stdout=f,stderr=subprocess.STDOUT)
 receipt=dict(modules=group,signature=signature,command=cmd,rc=r.returncode,seconds=time.monotonic()-t,log=str(log));(out/f'{i:04}.attempt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(i,r.returncode,round(receipt['seconds'],2),flush=True)
 if r.returncode in [124,137]:raise SystemExit(75)
 if r.returncode:raise SystemExit(1)
 assert all(sha((root/(m.replace('.','/')+'.lean')).read_bytes())==sources[m] for m in group)
 done.write_text(json.dumps(receipt,indent=2)+'\n')
assert all(sha((root/(m.replace('.','/')+'.lean')).read_bytes())==sources[m] for m in mods)
(out/'complete.json').write_text(json.dumps(dict(modules=len(mods),groups=len(groups),signature=signature,finished=time.time(),source_sha256=sources),indent=2)+'\n');print('TARGET BUILD COMPLETE',flush=True)
