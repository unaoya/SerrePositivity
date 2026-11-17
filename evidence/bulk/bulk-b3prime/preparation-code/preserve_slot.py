from pathlib import Path
import json,os,subprocess,time,hashlib,sys
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout').resolve();A=Path('/tmp/bulk-b3prime-preview').resolve();W=Path('/tmp/bulk-b3prime');budget=int(sys.argv[1]);start=time.monotonic();out=W/'preservation';out.mkdir(exist_ok=True);binary=Path('/tmp/bulk-w1-b2/private-snapshot/snapshot');rules=W/'owned-comparison-name-map.json';planpath=W/'preservation-module-plan.json';plan=json.loads(planpath.read_text());manifest=json.loads((W/'before-manifest.json').read_text());groups=manifest['groups'];signature=hashlib.sha256(json.dumps({'rules':hashlib.sha256(rules.read_bytes()).hexdigest(),'plan':hashlib.sha256(planpath.read_bytes()).hexdigest(),'binary':hashlib.sha256(binary.read_bytes()).hexdigest(),'comparator':hashlib.sha256((R/'scripts/refactor/bulk_compare.py').read_bytes()).hexdigest(),'after':json.loads((W/'final-bundle/manifest.json').read_text())['files']},sort_keys=True).encode()).hexdigest()
def environment(root):
 env=dict(os.environ,LEAN_NUM_THREADS='1');raw=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(os.pathsep);paths=[str((Path(p) if Path(p).is_absolute() else root/p).resolve()) for p in raw];env['LEAN_PATH']=os.pathsep.join(paths);env['LEAN_SYSROOT']=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip();assert str(root/'.lake/build/lib/lean') in paths
 other=A if root==R else R;assert str(other/'.lake/build/lib/lean') not in paths
 return env
assert hashlib.sha256(binary.read_bytes()).hexdigest()=='044d36482e16a0708bdb58e6b3f5cdbf1f53b5deec92e5921d07b290109d45b9','v3b binary differs from the unchanged established capture tool'
oldenv=environment(R);newenv=environment(A)
def after_modules(mods):
 result=set()
 for m in mods:
  if m=='SerrePositivity.Inputs.Perfectoidization':continue
  result.add(plan['modules'].get(m,m));result.update(plan.get('declarations',{}).get(m,{}).values())
 for m in result:assert (A/(m.replace('.','/')+'.lean')).exists(),m
 return sorted(result)
def capture(side,root,env,mods,dest):
 receipt=dest.with_suffix('.capture.json')
 if receipt.exists():
  old=json.loads(receipt.read_text())
  if old['signature']==signature and old['modules']==mods and old['snapshot_sha256']==hashlib.sha256(dest.read_bytes()).hexdigest():return
 left=int(budget-(time.monotonic()-start)-10)
 if left<45:raise SystemExit(75)
 log=dest.with_suffix('.log');t=time.monotonic();cmd=[str(binary),'--stable-project','--name-map',str(rules),'--modules',','.join(mods),'--output',str(dest)]
 with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(left),*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode in [124,137]:raise SystemExit(75)
 if r.returncode:raise RuntimeError(str({'side':side,'rc':r.returncode,'log':str(log)}))
 data=json.loads(dest.read_text());assert set(data['modules'])==set(mods);assert all((root/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in data['sources'])
 receipt.write_text(json.dumps({'signature':signature,'side':side,'modules':mods,'seconds':time.monotonic()-t,'snapshot_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()},indent=2))
def assess(comparison):
 explained=[];unexplained=[]
 for change in comparison['changes']:
  if change.get('change')=='removed' and change.get('name')=='SerrePositivity.Inputs.exists_perfectoidization_of_finite' and change.get('module')=='SerrePositivity.Inputs.Perfectoidization':explained.append({**change,'authorization':'R8-4 approved removal of wrapper whose proof is direct BS theorem; raw difference retained'})
  else:unexplained.append(change)
 return explained,unexplained
# Prioritize a previously failing group for feedback, still require every group.
order=sorted(range(len(groups)),key=lambda i: not ((p:=out/f'{i:03}'/'assessment.json').exists() and json.loads(p.read_text()).get('unexplained')))
for i in order:
 mods=groups[i]
 label=f'{i:03}';dest=out/label;dest.mkdir(exist_ok=True);done=dest/'assessment.json'
 if done.exists():
  previous=json.loads(done.read_text())
  if previous['signature']==signature and not previous['unexplained']:continue
 after=after_modules(mods)
 # Each original group has multiple surviving modules; no fabricated empty capture.
 assert after
 capture('before',R,oldenv,mods,dest/'before.json');capture('after',A,newenv,after,dest/'after.json')
 cmd=['python3',str(R/'scripts/refactor/bulk_compare.py'),str(dest/'before.json'),str(dest/'after.json'),'--name-map',str(rules),'--module-map',str(planpath),'--output',str(dest/'raw-comparison.json')]
 with (dest/'compare.log').open('w') as f:r=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode not in [0,1]:raise RuntimeError('comparator failed '+label)
 comparison=json.loads((dest/'raw-comparison.json').read_text());explained,unexplained=assess(comparison);record={'signature':signature,'original_modules':mods,'after_modules':after,'raw_status':comparison['status'],'before_count':comparison['before_count'],'after_count':comparison['after_count'],'explained':explained,'unexplained':unexplained};done.write_text(json.dumps(record,ensure_ascii=False,indent=2));print(label,comparison['status'],'explained',len(explained),'unexplained',len(unexplained),flush=True)
 if unexplained:raise SystemExit(1)
 if budget-(time.monotonic()-start)<60:raise SystemExit(75)
records=[json.loads((out/f'{i:03}'/'assessment.json').read_text()) for i in range(len(groups))];explained=[x for r in records for x in r['explained']];assert len(explained)==1,explained;(out/'complete.json').write_text(json.dumps({'signature':signature,'original_modules':sum(map(len,groups)),'groups':len(groups),'before_count':sum(r['before_count'] for r in records),'after_count':sum(r['after_count'] for r in records),'explained':explained,'unexplained':0,'finished':time.time()},ensure_ascii=False,indent=2));print('PRESERVATION COMPLETE',flush=True)
