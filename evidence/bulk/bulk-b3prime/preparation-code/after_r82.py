from pathlib import Path
import subprocess,os,time,json
R=Path('/tmp/bulk-b3prime-preview');W=Path('/tmp/bulk-b3prime');M='SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface';B=Path('/tmp/bulk-w1-b2/private-snapshot/snapshot');mods=[M,'SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCategories','SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingInterface'];steps=[]
for command in [['lake','build',*mods],['lake','env',str(B),'--stable-project','--modules',','.join(mods),'--output',str(W/'r82-after.json')]]:
 start=time.monotonic()
 with (W/('r82-after-'+str(len(steps))+'.log')).open('w') as f:r=subprocess.run(command,cwd=R,env=dict(os.environ,LEAN_NUM_THREADS='2'),stdout=f,stderr=subprocess.STDOUT)
 steps.append({'command':command,'rc':r.returncode,'seconds':time.monotonic()-start});print(steps[-1],flush=True);(W/'r82-after-receipt.json').write_text(json.dumps({'steps':steps},indent=2))
 if r.returncode:raise SystemExit(r.returncode)
d=json.loads((W/'r82-after.json').read_text());assert all((R/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in d['sources']);print('verified after snapshot',len(d['declarations']),flush=True)
