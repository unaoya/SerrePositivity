from pathlib import Path
import json,subprocess,time,os,hashlib
W=Path('/tmp/bulk-b3prime');R=Path('/tmp/bulk-b3prime-preview');rows=json.loads((W/'projected-generic-plan.json').read_text());mods=[r['new_module'] for r in rows];steps=[];status='PASS'
for label,cmd in [('build',['lake','build',*mods]),('snapshot',['lake','env','/tmp/bulk-w1-b2/private-snapshot/snapshot','--stable-project','--modules',','.join(mods),'--output',str(W/'generic-preview-snapshot.json')])]:
 start=time.monotonic()
 with (W/('generic-preview-'+label+'.log')).open('w') as f:r=subprocess.run(cmd,cwd=R,env=dict(os.environ,LEAN_NUM_THREADS='2'),stdout=f,stderr=subprocess.STDOUT)
 steps.append({'label':label,'command':cmd,'rc':r.returncode,'seconds':time.monotonic()-start});print(steps[-1],flush=True)
 if r.returncode:status='FAIL';break
if status=='PASS':
 d=json.loads((W/'generic-preview-snapshot.json').read_text());assert all((R/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in d['sources'])
receipt={'status':status,'scope':'three isolated generic target builds only; full original-owner v3b is still pending','steps':steps,'source_hashes':{m:hashlib.sha256((R/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in mods}};(W/'generic-preview-receipt.json').write_text(json.dumps(receipt,indent=2));print(status,flush=True)
# A failed independent feasibility probe is recorded, not a reason to abandon baseline captures.
