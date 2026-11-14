from pathlib import Path
import json,shutil,tarfile,gzip,hashlib,subprocess
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'formalization-plans/stage-ii/bulk-b3prime'
for script in ['check_actual_source_scope.py','check_actual_graph.py','check_r73_actual.py','check_audit_name_coverage.py','prepare_b4_lanes.py','completion_audit.py']:
 p=subprocess.run(['python3',str(W/script)]);assert p.returncode==0,script
completion=json.loads((W/'completion-audit.json').read_text());assert completion['all_passed'] and completion['scope_complete']==22
items=json.loads((W/'scope-items-applied.json').read_text());items.update(final_complete=22,final_gates='completion-audit.json',count_policy='All implementation rows and all final gates passed; already-main items remain identified.')
for row in items['items']:row['status']='already-main-complete' if row['status']=='already-main' else 'complete'
(W/'scope-items-complete.json').write_text(json.dumps(items,ensure_ascii=False,indent=2))
for name in ['actual-application.json','actual-source-scope-check.json','actual-import-graph.json','actual-layer-comparison.json','actual-citation-comparison.json','actual-citation-location-check.json','r7-3b-actual-edge-ledger.json','audit-name-coverage.json','audit-input-equivalence.json','audit-module-scope-coverage.json','root-build-complete.json','all-audit-inventory.json','all-audits-complete.json','full-verify-complete.json','full-verify-summary.json.gz','verify-resource-plan.json','verify-scheduling-telemetry.json','B4-regression-complete.json','completion-audit.json','scope-items-complete.json']:
 shutil.copy2(W/name,D/name)
for p in (W/'B4').iterdir():
 if p.is_file():shutil.copy2(p,D/'B4'/p.name)
for name in ['audit_input_scope.py','formal_audit_driver.py','full_verify_driver.py','continue_after_formal.py','continue_after_verify_b4.py','completion_audit.py','prepare_b4_import_owners.py','test_b4_preview.py','test_b4_native_after.py','prepare_b4_lanes.py','save_final_b3_evidence.py','write_final_b3_report.py']:
 shutil.copy2(W/name,D/'preparation-code'/name)
with tarfile.open(D/'formal-audits-and-full-verify.tar.gz','w:gz') as archive:
 archive.add(W/'all-audits',arcname='formal-audits')
 for name in ['all-audits-complete.json','full-verify.log','full-verify.log.json','full-verify-complete.json','full-verify-summary.json.gz','verify-resource-plan.json','verify-scheduling-telemetry.json']:
  archive.add(W/name,arcname=name)
 for p in (R/'.lake/verify').iterdir():
  if p.is_file():archive.add(p,arcname='verify/'+p.name)
with tarfile.open(D/'B4-tool-regression.tar.gz','w:gz') as archive:
 archive.add(W/'B4-tests-v4',arcname='B4-tests')
 for name in ['B4-regression-complete.json','B4-native-regression.log','B4-native-regression.log.json']:archive.add(W/name,arcname=name)
print('Final B3prime evidence saved; report and commit still required')
