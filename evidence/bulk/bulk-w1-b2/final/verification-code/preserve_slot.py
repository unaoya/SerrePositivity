from pathlib import Path
import os,json,subprocess,time,hashlib,threading,concurrent.futures
from capture_receipt import valid_capture,save_capture
from parallel_capture_transport import run_independent_captures,available_memory_bytes
W=Path('/tmp/bulk-w1-b2');V=W/'preview';R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');start=time.monotonic();BUDGET=int(os.environ.get('BULK_SLOT_SECONDS','548'));groups=json.loads((W/'preservation-groups.json').read_text());plan=json.loads((W/'preservation-module-plan.json').read_text());mm=plan['modules'];out=W/'preservation';out.mkdir(exist_ok=True);splitsfile=out/'splits.json';splits=json.loads(splitsfile.read_text()) if splitsfile.exists() else {};rules=W/'owned-comparison-name-map.json';maphash=hashlib.sha256(rules.read_bytes()).hexdigest();binary=W/'private-snapshot/snapshot';baseenv=dict(os.environ,LEAN_NUM_THREADS='2',LEAN_SYSROOT=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=V,text=True).strip());paths=[]
for raw in subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,text=True).strip().split(os.pathsep):
 p=Path(raw);paths.append((p if p.is_absolute() else V/p).resolve())
def after_modules(modules):
 return sorted({mm.get(m,m) for m in modules}|{d for m in modules for d in plan.get('declarations',{}).get(m,{}).values()})
global_after_signature=hashlib.sha256(json.dumps({m:hashlib.sha256((V/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in after_modules([m for group in groups for m in group])},sort_keys=True).encode()).hexdigest()
newbuild=(V/'.lake/build').resolve();oldbuild=(W/'baseline-build').resolve();oldenv=dict(baseenv,LEAN_PATH=os.pathsep.join(str(oldbuild/p.relative_to(newbuild)) if p.is_relative_to(newbuild) else str(p) for p in paths));newenv=dict(baseenv,LEAN_PATH=os.pathsep.join(map(str,paths)));assert str(oldbuild/'lib/lean') in oldenv['LEAN_PATH'];assert str(newbuild/'lib/lean') not in oldenv['LEAN_PATH'];errors=[];saved=0;transport_lock=threading.Lock()

binary_hash=hashlib.sha256(binary.read_bytes()).hexdigest();module_plan_hash=hashlib.sha256((W/'preservation-module-plan.json').read_bytes()).hexdigest()

def signature(modules):
 return hashlib.sha256(json.dumps({'module_plan_sha256':module_plan_hash,'snapshot_binary_sha256':binary_hash,'global_after_sources':global_after_signature,'modules':modules,'name_map':maphash,'comparator_sha256':hashlib.sha256((W/'bulk_compare.py').read_bytes()).hexdigest(),'before_sources':{m:hashlib.sha256((R/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in modules},'after_sources':{m:hashlib.sha256((V/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in after_modules(modules)},**({'strict_term_structure':True} if modules and all('.Project.Compatibility.' in m for m in modules) else {})},sort_keys=True).encode()).hexdigest()

def complete(modules,label):
 if label in splits:
  n=len(modules)//2;return complete(modules[:n],label+'a') and complete(modules[n:],label+'b')
 p=out/(label+'.receipt.json')
 return p.exists() and json.loads(p.read_text()).get('signature')==signature(modules) and json.loads(p.read_text()).get('status')=='PASS' and json.loads(p.read_text()).get('comparison_rc')==0

def one(modules,label):
 global saved
 if complete(modules,label):return
 if label in splits:
  n=len(modules)//2;one(modules[:n],label+'a');one(modules[n:],label+'b');return
 remaining=BUDGET-(time.monotonic()-start)
 if remaining<30:return
 destination=out/label;destination.mkdir(exist_ok=True);results=[];sig=signature(modules)
 def capture(spec):
  side,mods,root,env=spec;p=destination/(side+'.json');log=destination/(side+'.log')
  if valid_capture(p,sig,side,mods):
   old=json.loads(p.with_suffix('.capture.json').read_text());return {'side':side,'rc':0,'seconds':old.get('seconds',0),'reused_completed_capture':True}
  remaining=BUDGET-(time.monotonic()-start)
  if remaining<30:return {'side':side,'deferred':True}
  limit=min(330 if BUDGET>300 else 220,int(remaining-12));t=time.monotonic()
  with log.open('w') as f:r=subprocess.run(['gtimeout','--kill-after=3s',str(limit),'/usr/bin/time','-l','-o',str(destination/(side+'.resources')),str(binary),'--stable-project',*(['--no-proof-irrelevant'] if modules and all('.Project.Compatibility.' in m for m in modules) else []),'--name-map',str(rules),'--modules',','.join(mods),'--output',str(p)],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
  result={'side':side,'rc':r.returncode,'seconds':time.monotonic()-t,'limit_seconds':limit}
  if r.returncode:p.with_suffix('.capture.json').unlink(missing_ok=True);return result
  data=json.loads(p.read_text());assert set(data['modules'])==set(mods)
  assert all((root/(source['module'].replace('.','/')+'.lean')).read_text()==source['source'] for source in data['sources'])
  save_capture(p,sig,side,mods,result['seconds']);return result
 specs=[('before',modules,R,oldenv),('after',after_modules(modules),V,newenv)]
 results,parallelism,memory_available=run_independent_captures(specs,capture)
 for result in results:
  if result.get('deferred'):return
  if result['rc']:
   side=result['side'];limit=result['limit_seconds']
   if result['rc'] in [124,137] and limit<180:
    print('resume next slot',label,side,'short-tail budget',limit,flush=True);return
   if len(modules)>1:
    with transport_lock:
     splits[label]={'reason':'timeout/resource/import-union failure','side':side,'rc':result['rc']};splitsfile.write_text(json.dumps(splits,indent=2))
    print('split',label,len(modules),side,result['rc'],flush=True);return
   errors.append({'label':label,'modules':modules,'side':side,'rc':result['rc'],'log':str(destination/(side+'.log'))});return
 if BUDGET-(time.monotonic()-start)<12:return
 (destination/'comparison.json').unlink(missing_ok=True)
 with (destination/'compare.log').open('w') as f:r=subprocess.run(['python3','-B',str(W/'bulk_compare.py'),str(destination/'before.json'),str(destination/'after.json'),'--name-map',str(rules),'--module-map',str(W/'preservation-module-plan.json'),'--output',str(destination/'comparison.json')],cwd=V,stdout=f,stderr=subprocess.STDOUT)
 comparison=json.loads((destination/'comparison.json').read_text()) if r.returncode in [0,1] and (destination/'comparison.json').exists() else {};record={'modules':modules,'after_modules':after_modules(modules),'signature':sig,'environment_policy':'resolved-independent-baseline-v2','name_map_sha256':maphash,'comparator_sha256':hashlib.sha256((W/'bulk_compare.py').read_bytes()).hexdigest(),'results':results,'capture_parallelism':parallelism,'available_memory_at_capture':memory_available,'capture_policy':'independent-side-integrity-receipts-v3','comparison_rc':r.returncode,'status':comparison.get('status','ERROR'),'before_count':comparison.get('before_count'),'after_count':comparison.get('after_count'),'changes':len(comparison.get('changes',[]))};(out/(label+'.receipt.json')).write_text(json.dumps(record,indent=2));print(label,len(modules),record['status'],record['changes'],flush=True)
 if r.returncode:errors.append(record|{'label':label,'comparison':str(destination/'comparison.json')})
 else:
  with transport_lock:saved+=len(modules)
# The comment overlay uses a separate artifact tree. Validate a bounded piece
# inside this same acquired lease, never queueing a second ticket. R -> V and
# V -> replay-tree are independent until their final transitive report.
if not (W/'bounded-doc-supplement-complete.json').exists() and BUDGET-(time.monotonic()-start)>180:
 with (W/'bounded-doc-check-in-preservation.log').open('a') as log:
  doc=subprocess.run(['gtimeout','--kill-after=3s','125','python3','-B',str(W/'doc_supplement_slot.py')],cwd=W/'replay-tree',env=dict(os.environ,BULK_SLOT_SECONDS='110'),stdout=log,stderr=subprocess.STDOUT)
 if doc.returncode not in [0,124,137]:raise SystemExit(doc.returncode)
ordered_groups=sorted(enumerate(groups),key=lambda pair: not any('.Andre.PowerRootEnvelope.Audit.' in m for m in pair[1]))
pending=[(i,modules) for i,modules in ordered_groups if not complete(modules,f'{i:04}')]
# Four native readers at most, below the measured B2 32 GiB envelope. A group
# containing a standalone script is kept serial, and each inner pair also has
# its own 20 GiB guard. All processes remain within this one 280-second lease.
width=2 if available_memory_bytes()>=28*1024**3 and all(all(m.startswith('SerrePositivity.') for m in ms) for _,ms in pending) else 1
print('independent group lanes',width,flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=width) as pool:
 for at in range(0,len(pending),width):
  futures=[pool.submit(one,modules,f'{i:04}') for i,modules in pending[at:at+width]]
  for future in futures:future.result()
  if errors or time.monotonic()-start>BUDGET-40:break
if errors:(W/'preservation-errors.json').write_text(json.dumps(errors,indent=2));raise SystemExit(1)
if all(complete(modules,f'{i:04}') for i,modules in enumerate(groups)):(W/'preservation-complete.json').write_text(json.dumps({'modules':sum(map(len,groups)),'finished':time.time(),'policy':'v3b stable-project, same name map; independent before/after artifact roots'}))
print('preserved this slot',saved,'seconds',time.monotonic()-start,flush=True)
