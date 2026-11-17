from pathlib import Path
import json,subprocess,time,os,hashlib
W=Path('/tmp/bulk-w1-b3');V=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');start=time.monotonic();BUDGET=int(os.environ.get('BULK_SLOT_SECONDS','1200'));out=W/'moved-audit-checks';out.mkdir(exist_ok=True);paths=json.load(open(W/'evening-audit-plan.json'))['standalone_audits'];results=[]
for rel in paths:
 p=V/rel;digest=hashlib.sha256(p.read_bytes()).hexdigest();receipt=out/(p.stem+'.json')
 if receipt.exists():
  result=json.load(open(receipt))
  if result.get('rc')==0 and result.get('source_sha256')==digest and result.get('verification_module_name')==rel[:-5].replace('/','.'):results.append(result);continue
 remaining=int(BUDGET-(time.monotonic()-start))
 if remaining<25:break
 artifact=V/'.lake/build/lib/lean'/Path(rel).with_suffix('.olean');artifact.parent.mkdir(parents=True,exist_ok=True);index=artifact.with_suffix('.ilean')
 setup=out/(p.stem+'.setup.json');configured=subprocess.run(['gtimeout','30','lake','--no-build','setup-file',rel],cwd=V,text=True,capture_output=True)
 if configured.returncode:raise SystemExit(configured.returncode)
 original_setup=json.loads(configured.stdout);assert original_setup['options']['maxSynthPendingDepth']==3
 (out/(p.stem+'.original-lake-setup.json')).write_text(configured.stdout)
 # Lake gives standalone scripts the non-importable name _unknown. The temporary
 # preservation artifact needs its path-derived module identity; all options/imports stay unchanged.
 configured_setup=dict(original_setup,name=rel[:-5].replace('/','.'))
 setup.write_text(json.dumps(configured_setup))
 t=time.monotonic()
 with (out/(p.stem+'.log')).open('w') as log:r=subprocess.run(['gtimeout','--kill-after=3s',str(min(remaining,220)),'lake','env','lean','--setup='+str(setup),'--root='+str(V),'-o',str(artifact),'-i',str(index),rel],cwd=V,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT)
 result={'path':rel,'source_sha256':digest,'lake_setup_sha256':hashlib.sha256(setup.read_bytes()).hexdigest(),'rc':r.returncode,'seconds':time.monotonic()-t,'lake_standalone_module_name':original_setup['name'],'verification_module_name':configured_setup['name'],'lake_options_preserved':configured_setup['options']==original_setup['options']};receipt.write_text(json.dumps(result,indent=2));print(rel,r.returncode,round(result['seconds'],2),flush=True)
 if r.returncode==0:assert json.load(open(index))['module']==rel[:-5].replace('/','.'),rel
 if r.returncode:raise SystemExit(0 if r.returncode in [124,137] else r.returncode)
 results.append(result)
if len(results)==len(paths):(W/'moved-audits-complete.json').write_text(json.dumps({'audits':results,'scope':'four relocated destinations only; full B3 audits not run'},indent=2))
