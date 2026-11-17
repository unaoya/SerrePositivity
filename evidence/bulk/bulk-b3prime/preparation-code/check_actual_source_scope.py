from pathlib import Path
import json,subprocess,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');a=json.loads((W/'actual-application.json').read_text());paths=subprocess.check_output(['git','diff','391b2a0d2','HEAD','--name-only','--no-renames'],cwd=R,text=True).splitlines();core=[p for p in paths if p=='SerrePositivity.lean' or p.startswith(('SerrePositivity/','scripts/')) or (p.startswith('formalization-plans/bhatt-scholze/drafts/') and p.endswith('.lean')) or p in ['lakefile.toml','lean-toolchain','lake-manifest.json']];allowed=set(a['paths_written']);deleted=set(a['delete_paths']);assert set(core)<=allowed|deleted,sorted(set(core)-allowed-deleted)
for p,h in a['paths_written'].items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h,p
for p in deleted:assert not (R/p).exists(),p
unchanged=[]
for p in sorted(allowed-set(core)):
 original=subprocess.check_output(['git','show','391b2a0d2:'+p],cwd=R);assert original==(R/p).read_bytes(),p;unchanged.append(p)
res={'main':'391b2a0d2','own_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'changed_core_script_draft_paths':len(core),'authorized_writes':len(allowed),'authorized_deletions':len(deleted),'prepared_identical_to_main':unchanged,'outside_scope_core_script_draft_changes':[],'hash_mismatches':[],'statement_proof_change_policy':'Only authorized whole moves/splits/name and import transport, explicit original Finite telescope restoration, comments, and one approved wrapper deletion. Strict native v3b provides semantic gate.','mathematical_tooling_unchanged':['bulk_snapshot.py','bulk_compare.py','bulk_namespace.py','klw1_namespace.py','verify.sh','verify_runner.py']}
for p in res['mathematical_tooling_unchanged']:assert subprocess.check_output(['git','diff','391b2a0d2','HEAD','--','scripts/refactor/'+p],cwd=R)==b'',p
(W/'actual-source-scope-check.json').write_text(json.dumps(res,ensure_ascii=False,indent=2));print({k:v for k,v in res.items() if not isinstance(v,list)});print('unchanged prepared',len(unchanged))
