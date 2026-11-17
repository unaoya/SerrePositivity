"""Bounded independent before/after captures with the unchanged B3 v3b comparator."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--before-root',type=Path,required=True);p.add_argument('--after-root',type=Path,required=True);p.add_argument('--modules',type=Path,required=True);p.add_argument('--name-map',type=Path,required=True);p.add_argument('--module-plan',type=Path,required=True);p.add_argument('--snapshot',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--budget',type=int,default=265);a=p.parse_args();start=time.monotonic();a.output.mkdir(parents=True,exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text());modules=load(a.modules);plan=load(a.module_plan);mm=plan['modules'];assert sha(a.snapshot)=='044d36482e16a0708bdb58e6b3f5cdbf1f53b5deec92e5921d07b290109d45b9';comparator=a.after_root/'scripts/refactor/bulk_compare.py';rules_sha=sha(a.name_map)
roots={'before':a.before_root.resolve(),'after':a.after_root.resolve()};assert (roots['before']/'.lake/build').resolve()!=(roots['after']/'.lake/build').resolve()
source_hashes={side:{m:sha(root/(m.replace('.','/')+'.lean')) for m in (modules if side=='before' else [mm.get(m,m) for m in modules])} for side,root in roots.items()}
signature=hashlib.sha256(json.dumps(dict(sources=source_hashes,rules=rules_sha,module_plan=sha(a.module_plan),binary=sha(a.snapshot),comparator=sha(comparator),policy='unchanged B3 stable-project v3b; independent artifact roots'),sort_keys=True).encode()).hexdigest();group_file=a.output/'groups.json'
if group_file.exists():groups=load(group_file);assert groups['signature']==signature
else:
 groups=dict(signature=signature,groups=[dict(label=f'{i//64:04}',modules=modules[i:i+64]) for i in range(0,len(modules),64)]);group_file.write_text(json.dumps(groups,indent=2)+'\n')
envs={}
for side,root in roots.items():
 prefix=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip();paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(os.pathsep);resolved=[str((Path(p) if Path(p).is_absolute() else root/p).resolve()) for p in paths];assert str((root/'.lake/build/lib/lean').resolve()) in resolved
 other=roots['after' if side=='before' else 'before'];assert str((other/'.lake/build/lib/lean').resolve()) not in resolved;envs[side]=os.environ|{'LEAN_NUM_THREADS':'1','LEAN_SYSROOT':prefix,'LEAN_PATH':os.pathsep.join(resolved)}
assert envs['before']['LEAN_SYSROOT']==envs['after']['LEAN_SYSROOT']
def actual_modules(side,group):return group if side=='before' else [mm.get(m,m) for m in group]
def valid(group,side):
 directory=a.output/group['label'];receipt=directory/(side+'.receipt.json');data=directory/(side+'.json')
 if not receipt.exists() or not data.exists():return False
 r=load(receipt);return r['signature']==signature and r['modules']==actual_modules(side,group['modules']) and r['returncode']==0 and r['capture_sha256']==sha(data)
def capture(spec):
 group,side=spec;directory=a.output/group['label'];directory.mkdir(exist_ok=True)
 if valid(group,side):return dict(side=side,returncode=0,reused=True)
 remaining=a.budget-(time.monotonic()-start)
 if remaining<80:return dict(side=side,deferred=True)
 limit=max(1,min(235,int(remaining-15)));data=directory/(side+'.json');data.unlink(missing_ok=True);t=time.monotonic();mods=actual_modules(side,group['modules']);command=[str(a.snapshot),'--stable-project','--name-map',str(a.name_map),'--modules',','.join(mods),'--output',str(data)]
 with (directory/(side+'.log')).open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(limit),*command],cwd=roots[side],env=envs[side],stdout=f,stderr=subprocess.STDOUT)
 record=dict(side=side,signature=signature,modules=mods,returncode=r.returncode,seconds=time.monotonic()-t,limit_seconds=limit,root=str(roots[side]))
 if r.returncode==0:
  native=load(data);assert set(native['modules'])==set(mods);assert {s['module'] for s in native['sources']}==set(mods)
  for s in native['sources']:assert hashlib.sha256(s['source'].encode()).hexdigest()==source_hashes[side][s['module']]
  record.update(capture_sha256=sha(data),declarations=native['count'],huge_terms=len(native['huge_terms']));(directory/(side+'.receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
 else:data.unlink(missing_ok=True)
 return record
def available_memory():
 try:
  raw=subprocess.check_output(['vm_stat'],text=True);size=int(re.search(r'page size of (\d+) bytes',raw)[1]);return size*sum(int(re.search(r'Pages '+x+r':\s+(\d+)',raw)[1]) for x in ['free','inactive','speculative'])
 except (OSError,ValueError,TypeError,subprocess.SubprocessError):return 0
def comparison_valid(group):
 directory=a.output/group['label'];receipt=directory/'comparison-receipt.json';data=directory/'comparison.json'
 if not receipt.exists() or not data.exists() or not all(valid(group,side) for side in roots):return False
 r=load(receipt);c=load(data)
 return r.get('signature')==signature and r.get('status')=='PASS' and r.get('comparison_sha256')==sha(data) and c.get('status')=='PASS' and c.get('changes')==[]
failure=None
for group in list(groups['groups']):
 directory=a.output/group['label'];done=directory/'comparison-receipt.json'
 if comparison_valid(group):continue
 if a.budget-(time.monotonic()-start)<100:break
 specs=[(group,side) for side in roots];workers=2 if available_memory()>=20*1024**3 else 1
 with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:results=list(pool.map(capture,specs))
 errors=[r for r in results if r.get('returncode',0)!=0]
 if errors:
  if all(r['returncode'] in [124,137] for r in errors) and len(group['modules'])>1:
   n=len(group['modules'])//2;i=groups['groups'].index(group);groups['groups'][i:i+1]=[dict(label=group['label']+'a',modules=group['modules'][:n]),dict(label=group['label']+'b',modules=group['modules'][n:])];group_file.write_text(json.dumps(groups,indent=2)+'\n');print('Split for a future lease',group['label'],flush=True);break
  failure=dict(group=group,results=results);break
 if not all(valid(group,side) for side in roots):break
 with (directory/'compare.log').open('w') as f:r=subprocess.run(['python3',str(comparator),str(directory/'before.json'),str(directory/'after.json'),'--name-map',str(a.name_map),'--module-map',str(a.module_plan),'--output',str(directory/'comparison.json')],cwd=roots['after'],stdout=f,stderr=subprocess.STDOUT)
 comparison=load(directory/'comparison.json') if (directory/'comparison.json').exists() else {};record=dict(signature=signature,modules=group['modules'],results=results,parallel_readers=workers,comparison_returncode=r.returncode,status=comparison.get('status','ERROR'),changes=len(comparison.get('changes',[])),comparison_sha256=sha(directory/'comparison.json') if comparison else None);done.write_text(json.dumps(record,indent=2)+'\n');print('v3b',group['label'],len(group['modules']),record['status'],record['changes'],flush=True)
 if r.returncode or record['status']!='PASS':failure=record;break
completed=[]
for group in groups['groups']:
 path=a.output/group['label']/'comparison-receipt.json'
 if comparison_valid(group):completed+=group['modules']
summary=dict(signature=signature,completed_modules=len(completed),total_modules=len(modules),complete=len(completed)==len(modules),failure=failure,seconds=time.monotonic()-start,policy='Unchanged B3 v3b capture/comparison; same rules on independently built artifact roots');(a.output/'progress.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary));raise SystemExit(bool(failure))
