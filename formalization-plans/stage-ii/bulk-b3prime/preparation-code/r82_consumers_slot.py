from pathlib import Path
import json,subprocess,time,os
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');A=Path('/tmp/bulk-b3prime-preview');B=Path('/tmp/bulk-w1-b2/private-snapshot/snapshot');mods=[r['path'][:-5].replace('/','.') for r in json.loads((W/'r82-consumers.json').read_text())];steps=[]
for side,root in [('before',R),('after',A)]:
 for label,cmd in [('build',['lake','build',*mods]),('snapshot',['lake','env',str(B),'--stable-project','--modules',','.join(mods),'--output',str(W/f'r82-consumers-{side}.json')])]:
  start=time.monotonic()
  with (W/f'r82-consumers-{side}-{label}.log').open('w') as f:r=subprocess.run(cmd,cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='2'),stdout=f,stderr=subprocess.STDOUT)
  row={'side':side,'label':label,'command':cmd,'rc':r.returncode,'seconds':time.monotonic()-start};steps.append(row);print(row,flush=True);(W/'r82-consumers-receipt.json').write_text(json.dumps(steps,indent=2))
  if r.returncode:raise SystemExit(r.returncode)
 d=json.loads((W/f'r82-consumers-{side}.json').read_text());assert all((root/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in d['sources'])
cmd=['python3',str(R/'scripts/refactor/bulk_compare.py'),str(W/'r82-consumers-before.json'),str(W/'r82-consumers-after.json'),'--output',str(W/'r82-consumers-comparison.json')];r=subprocess.run(cmd,cwd=R);raise SystemExit(r.returncode)
