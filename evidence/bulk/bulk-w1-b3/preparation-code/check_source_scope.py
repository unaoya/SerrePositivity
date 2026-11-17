"""Full Lean-tree fidelity: frozen sources + approved bundle + indexed rewrites."""
from pathlib import Path
import sys,json,gzip,subprocess,hashlib
w=Path('/tmp/bulk-w1-b3');b=w/'before';r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(r/'scripts/refactor'));from bulk_apply_preview import replay
from audit_name_corrections import apply as correct_audit_names
correction_paths={x['path'] for x in json.load(open(w/'audit-declaration-name-corrections.json'))['fixes']}
sha=lambda data:hashlib.sha256(data).hexdigest()
bundle=json.loads(gzip.decompress((w/'initial-rebased-bundle.json.gz').read_bytes()));assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=b,text=True).strip()==bundle['math_base']
paths=lambda root,args:[p for p in subprocess.check_output(['git','ls-files',*args,'-z','--','*.lean'],cwd=root).decode().split('\0') if p and (root/p).is_file()]
original=paths(b,[]);expected={p:sha((b/p).read_bytes()) for p in original};original_count=len(expected)
for rel,signature in bundle['sources'].items():assert sha((b/rel).read_bytes())==signature,rel
for rel in bundle['deletions']:
 if rel.endswith('.lean'):assert rel in expected;expected.pop(rel)
initial_outputs=0
for row in bundle['outputs']:
 if not row['target'].endswith('.lean'):continue
 source=(b/row['source']).read_bytes() if row['source'] else b'';payload=replay(source,row['edits']);assert sha(payload)==row['sha256'];expected[row['target']]=sha(correct_audit_names(row['target'],payload)) if row['target'] in correction_paths else row['sha256'];initial_outputs+=1
rewrites=json.load(open(w/'delta-rewrite-status.json'));assert not correction_paths&{row['target'] for row in rewrites['rows'].values()};assert rewrites['files']==686 and not rewrites['review'];assert set(rewrites['rows'])==set(json.load(open(w/'delta-files.json')))
for rel,row in rewrites['rows'].items():
 target=row['target'];payload=(w/'rewritten-delta'/target).read_bytes();expected[target]=sha(payload)
actual_paths=set(paths(r,['-co','--exclude-standard']));missing=sorted(expected.keys()-actual_paths);extra=sorted(actual_paths-expected.keys());different=[p for p in expected.keys()&actual_paths if sha((r/p).read_bytes())!=expected[p]]
summary={'status':'FAIL' if missing or extra or different else 'PASS','original_lean_files':original_count,'expected_final_lean_files':len(expected),'actual_lean_files':len(actual_paths),'approved_initial_lean_outputs':initial_outputs,'indexed_frozen_main_rewrites':len(rewrites['rows']),'missing':missing,'extra':extra,'different':different,'input_bundle_sha256':sha((w/'initial-rebased-bundle.json.gz').read_bytes()),'mechanical_audit_constant_name_corrections':2,'audit_correction_ledger_sha256':sha((w/'audit-declaration-name-corrections.json').read_bytes()),'audit_correction_helper_sha256':sha((w/'audit_name_corrections.py').read_bytes()),'final_tree_sha256':sha(json.dumps(expected,sort_keys=True).encode()),'policy':'Every tracked original Lean file, including nonbuild drafts, plus the authorized rebased bundle and exact compiler-indexed delta outputs; two explicitly recorded audit declaration-name corrections derived from frozen declaration identity; no unaccounted Lean addition, deletion or edit accepted.'};(w/'full-source-scope-check.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print(summary);raise SystemExit(summary['status']!='PASS')
