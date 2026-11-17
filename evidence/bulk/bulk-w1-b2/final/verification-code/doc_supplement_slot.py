"""Validate a bounded comment-only supplement after full mathematical preservation."""
from pathlib import Path
import json,hashlib,subprocess,os,time,sys
w=Path('/tmp/bulk-w1-b2');v=w/'preview';t=w/'replay-tree';r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');out=w/'bounded-doc-check';out.mkdir(exist_ok=True);start=time.monotonic();budget=int(os.environ.get('BULK_SLOT_SECONDS','250'));plan=json.load(open(w/'bounded-doc-supplement-plan.json'));env=dict(os.environ,LEAN_NUM_THREADS='2')
def available():return int(budget-(time.monotonic()-start))
for i,row in enumerate(plan['rows']):
 receipt=out/f'build-{i:02}.json';p=t/row['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==row['after_sha256']
 if receipt.exists():assert json.load(open(receipt))['rc']==0;continue
 if available()<35:raise SystemExit(0)
 cmd=['lake','build',row['module']]
 if row['path'].startswith('scripts/'):
  setup=json.loads(subprocess.check_output(['lake','--no-build','setup-file',row['path']],cwd=t,text=True));assert setup['options']['maxSynthPendingDepth']==3;setup['name']=row['module'];sp=out/f'audit-{i}.setup.json';sp.write_text(json.dumps(setup));artifact=t/'.lake/build/lib/lean'/(row['module'].replace('.','/')+'.olean');artifact.parent.mkdir(parents=True,exist_ok=True)
  cmd=['lake','env','lean','--setup='+str(sp),'--root='+str(t),'-o',str(artifact),'-i',str(artifact.with_suffix('.ilean')),row['path']]
 began=time.monotonic()
 with (out/f'build-{i:02}.log').open('w') as f:p=subprocess.run(['gtimeout','--kill-after=3s',str(min(available()-5,210)),*cmd],cwd=t,env=env,stdout=f,stderr=subprocess.STDOUT)
 if p.returncode in [124,137]:raise SystemExit(0)
 if p.returncode:raise SystemExit(p.returncode)
 pub=t/'.lake/build/lib/lean'/(row['module'].replace('.','/')+'.olean');record={**row,'rc':p.returncode,'seconds':time.monotonic()-began,'after_public_olean_sha256':hashlib.sha256(pub.read_bytes()).hexdigest()};record['public_olean_unchanged']=record['before_public_olean_sha256']==record['after_public_olean_sha256'];receipt.write_text(json.dumps(record,indent=2));print('doc target',i,record['seconds'],record['public_olean_unchanged'],flush=True)
identity={'modules':{row['module']:row['module'] for row in plan['rows']}};(out/'module-plan.json').write_text(json.dumps(identity))
modules=','.join(identity['modules']);rules=w/'owned-comparison-name-map.json';binary=w/'private-snapshot/snapshot'
for side,root in [('before',v),('after',t)]:
 dest=out/(side+'.json')
 if dest.exists():continue
 if available()<55:raise SystemExit(0)
 paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(os.pathsep);capture=dict(env,LEAN_PATH=os.pathsep.join(str((Path(x) if Path(x).is_absolute() else root/x).resolve()) for x in paths),LEAN_SYSROOT=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip())
 with (out/(side+'.log')).open('w') as f:p=subprocess.run(['gtimeout','--kill-after=3s',str(min(available()-10,150)),str(binary),'--stable-project','--name-map',str(rules),'--modules',modules,'--output',str(dest)],cwd=root,env=capture,stdout=f,stderr=subprocess.STDOUT)
 if p.returncode:dest.unlink(missing_ok=True);raise SystemExit(0 if p.returncode in [124,137] else p.returncode)
for side,root in [('before',v),('after',t)]:
 d=json.load(open(out/(side+'.json')));assert set(d['modules'])==set(identity['modules']);assert all((root/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in d['sources'])
with (out/'compare.log').open('w') as f:p=subprocess.run(['python3','-B',str(r/'scripts/refactor/bulk_compare.py'),str(out/'before.json'),str(out/'after.json'),'--name-map',str(rules),'--module-map',str(out/'module-plan.json'),'--output',str(out/'comparison.json')],stdout=f,stderr=subprocess.STDOUT)
if p.returncode:raise SystemExit(p.returncode)
if not (out/'metadata.json').exists():
 if available()<75:raise SystemExit(0)
 subprocess.run(['python3','-B',str(w/'check_doc_metadata.py')],check=True)
comparison=json.load(open(out/'comparison.json'));assert comparison['status']=='PASS' and not comparison['changes'];builds=[json.load(open(out/f'build-{i:02}.json')) for i in range(14)];summary={'status':'PASS','scope':'Comment-only supplement, V -> independent replay tree, after the full R -> V preservation; production untouched. Broad R21 legacy prose is excluded.','files':14,'builds':builds,'before_count':comparison['before_count'],'after_count':comparison['after_count'],'unexplained_changes':0,'public_olean_unchanged':sum(x['public_olean_unchanged'] for x in builds),'finished':time.time()};(w/'bounded-doc-supplement-complete.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('14 docstrings built and preserved',flush=True)
