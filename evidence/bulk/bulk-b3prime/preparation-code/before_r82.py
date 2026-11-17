from pathlib import Path
import subprocess,os,time,json,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');M='SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface';B=Path('/tmp/bulk-w1-b2/private-snapshot/snapshot');source=R/'scripts/refactor/decl_snapshot.lean'
receipt=json.loads(B.with_name('receipt.json').read_text());assert hashlib.sha256(source.read_bytes()).hexdigest()==receipt['original_source_sha256'];assert hashlib.sha256(B.read_bytes()).hexdigest()==receipt['binary_sha256']
steps=[]
for command in [['lake','build',M],['lake','env',str(B),'--stable-project','--modules',M,'--output',str(W/'r82-before.json')]]:
 start=time.monotonic()
 with (W/('r82-before-'+str(len(steps))+'.log')).open('w') as f:r=subprocess.run(command,cwd=R,env=dict(os.environ,LEAN_NUM_THREADS='2'),stdout=f,stderr=subprocess.STDOUT)
 steps.append({'command':command,'rc':r.returncode,'seconds':time.monotonic()-start});print(steps[-1],flush=True)
 (W/'r82-before-receipt.json').write_text(json.dumps({'steps':steps,'snapshot_binary_sha256':receipt['binary_sha256']},indent=2))
 if r.returncode:raise SystemExit(r.returncode)
d=json.loads((W/'r82-before.json').read_text());assert all((R/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in d['sources']);print('verified source snapshot',len(d['declarations']),flush=True)
