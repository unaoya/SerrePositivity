from pathlib import Path
import subprocess,json,hashlib,time
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');manifest=W/'final-bundle/manifest.json';start_sig=hashlib.sha256(manifest.read_bytes()).hexdigest();assert (W/'target-build/complete.json').exists(),'finish current target stage first'
expected_target_sig=hashlib.sha256(json.dumps(json.loads(manifest.read_text())['files'],sort_keys=True).encode()).hexdigest();assert json.loads((W/'target-build/complete.json').read_text())['signature']==expected_target_sig,'stale target completion'
for script,args in [('prepare_owned_rules.py',[]),('run_leased_stage.py',['preservation']),('run_leased_stage.py',['citations-before']),('run_leased_stage.py',['citations-after']),('compare_citations.py',[])]:
 assert hashlib.sha256(manifest.read_bytes()).hexdigest()==start_sig,'source generation changed during preparation gates'
 print('starting',script,*args,flush=True);r=subprocess.run(['python3',str(W/script),*args],cwd=R)
 if r.returncode:raise SystemExit(r.returncode)
summary={'status':'isolated preparation gates passed; actual branch application, refreshed main and final root/audits/verify still pending','source_manifest_sha256':start_sig,'target':json.loads((W/'target-build/complete.json').read_text()),'preservation':json.loads((W/'preservation/complete.json').read_text()),'citation_comparison':json.loads((W/'citation-comparison.json').read_text()),'time':time.time()};(W/'preparation-complete.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('ISOLATED PREPARATION COMPLETE; NOT APPLIED',flush=True)
