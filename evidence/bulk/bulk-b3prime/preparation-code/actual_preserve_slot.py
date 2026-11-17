from pathlib import Path
import json,hashlib,subprocess,os,time,sys
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout').resolve();A=Path('/tmp/bulk-b3prime-preview').resolve();budget=int(sys.argv[1]);start=time.monotonic();out=W/'actual-preservation';out.mkdir(exist_ok=True);binary=Path('/tmp/bulk-w1-b2/private-snapshot/snapshot');rules=W/'owned-comparison-name-map.json';plan=W/'preservation-module-plan.json';complete=json.loads((W/'preservation/complete.json').read_text());application=json.loads((W/'actual-application.json').read_text());signature=hashlib.sha256(json.dumps({'application':application['paths_written'],'rules':hashlib.sha256(rules.read_bytes()).hexdigest(),'plan':hashlib.sha256(plan.read_bytes()).hexdigest()},sort_keys=True).encode()).hexdigest();env=dict(os.environ,LEAN_NUM_THREADS='1');paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip().split(os.pathsep);env['LEAN_PATH']=os.pathsep.join(str((Path(p) if Path(p).is_absolute() else R/p).resolve()) for p in paths);assert str(R/'.lake/build/lib/lean') in env['LEAN_PATH'] and str(A/'.lake/build/lib/lean') not in env['LEAN_PATH'];env['LEAN_SYSROOT']=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=R,text=True).strip();assert hashlib.sha256(binary.read_bytes()).hexdigest()=='044d36482e16a0708bdb58e6b3f5cdbf1f53b5deec92e5921d07b290109d45b9'
results=[]
for i in range(complete['groups']):
 original=W/'preservation'/f'{i:03}';baseline=original/'before.json';capture=json.loads((original/'before.capture.json').read_text());assert hashlib.sha256(baseline.read_bytes()).hexdigest()==capture['snapshot_sha256'];prepared=json.loads((original/'assessment.json').read_text());assert prepared['signature']==complete['signature'] and not prepared['unexplained'];mods=prepared['after_modules'];dest=out/f'{i:03}';dest.mkdir(exist_ok=True);receipt=dest/'assessment.json'
 if receipt.exists():
  old=json.loads(receipt.read_text())
  if old['signature']==signature and not old['unexplained']:results.append(old);continue
 # The same raw-name rules are used; check every source-private binding against
 # the already validated independent preview before relying on its rules.
 for m in mods:
  rel=m.replace('.','/')+'.ilean';before_decls=json.loads((A/'.lake/build/lib/lean'/rel).read_text())['decls'];actual_decls=json.loads((R/'.lake/build/lib/lean'/rel).read_text())['decls'];before_private={n for n in before_decls if n.startswith('_private.')};actual_private={n for n in actual_decls if n.startswith('_private.')};assert before_private==actual_private,('actual private identity changed; reconcile before recapture',m,before_private^actual_private)
 left=int(budget-(time.monotonic()-start)-10)
 if left<45:raise SystemExit(75)
 after=dest/'after.json';cmd=[str(binary),'--stable-project','--name-map',str(rules),'--modules',','.join(mods),'--output',str(after)]
 with (dest/'capture.log').open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(left),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode in [124,137]:raise SystemExit(75)
 if r.returncode:raise SystemExit(r.returncode)
 data=json.loads(after.read_text());assert set(data['modules'])==set(mods);assert all((R/(s['module'].replace('.','/')+'.lean')).read_text()==s['source'] for s in data['sources'])
 with (dest/'compare.log').open('w') as f:r=subprocess.run(['python3',str(R/'scripts/refactor/bulk_compare.py'),str(baseline),str(after),'--name-map',str(rules),'--module-map',str(plan),'--output',str(dest/'raw-comparison.json')],cwd=R,stdout=f,stderr=subprocess.STDOUT)
 assert r.returncode in [0,1];raw=json.loads((dest/'raw-comparison.json').read_text());explained=[];unexplained=[]
 for change in raw['changes']:
  if change.get('change')=='removed' and change.get('name')=='SerrePositivity.Inputs.exists_perfectoidization_of_finite' and change.get('module')=='SerrePositivity.Inputs.Perfectoidization':explained.append(change)
  else:unexplained.append(change)
 result={'signature':signature,'original_modules':prepared['original_modules'],'after_modules':mods,'before_snapshot_sha256':capture['snapshot_sha256'],'after_snapshot_sha256':hashlib.sha256(after.read_bytes()).hexdigest(),'before_count':raw['before_count'],'after_count':raw['after_count'],'explained':explained,'unexplained':unexplained};receipt.write_text(json.dumps(result,ensure_ascii=False,indent=2));results.append(result);print(i,'actual unexplained',len(unexplained),'approved deletions',len(explained),flush=True)
 if unexplained:raise SystemExit(1)
explained=[c for r in results for c in r['explained']];assert len(explained)==1;(out/'complete.json').write_text(json.dumps({'signature':signature,'groups':len(results),'original_modules':sum(len(r['original_modules']) for r in results),'before_count':sum(r['before_count'] for r in results),'after_count':sum(r['after_count'] for r in results),'unexplained':0,'explained':explained,'same_rule_sha256':hashlib.sha256(rules.read_bytes()).hexdigest(),'baseline':'stored independently captured original32d364b53 snapshots, never recaptured from mutated own worktree','time':time.time()},ensure_ascii=False,indent=2));print('ACTUAL PRESERVATION COMPLETE',flush=True)
