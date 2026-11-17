from pathlib import Path
import json,shutil,tarfile,subprocess,datetime
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'evidence/bulk/bulk-b3prime'
for script in ['check_actual_source_scope.py','check_actual_graph.py','check_r73_actual.py','check_audit_name_coverage.py','prepare_b4_lanes.py']:
 subprocess.run(['python3',str(W/script)],check=True)
subprocess.run(['python3',str(W/'completion_audit.py')])
c=json.loads((W/'completion-audit.json').read_text());assert c['passed']==16 and c['total_checks']==17 and not c['all_passed']
a=json.loads((W/'all-audits-complete.json').read_text());v=json.loads((W/'full-verify.log.json').read_text());assert a['success']==106 and v['reason']=='memory budget 32 GB'
for name in ['actual-source-scope-check.json','actual-import-graph.json','actual-citation-location-check.json','r7-3b-actual-edge-ledger.json','audit-name-coverage.json','audit-input-equivalence.json','audit-module-scope-coverage.json','root-build-complete.json','all-audit-inventory.json','all-audits-complete.json','verify-resource-plan.json','verify-scheduling-telemetry.json','B4-regression-complete.json','completion-audit.json']:
 shutil.copy2(W/name,D/name)
for p in (W/'B4').iterdir():
 if p.is_file():shutil.copy2(p,D/'B4'/p.name)
for name in ['audit_input_scope.py','formal_audit_driver.py','full_verify_driver.py','continue_after_formal.py','continue_after_verify_b4.py','completion_audit.py','prepare_b4_import_owners.py','test_b4_preview.py','test_b4_native_after.py','prepare_b4_lanes.py','save_final_b3_evidence.py','write_final_b3_report.py','save_checkpoint.py']:
 shutil.copy2(W/name,D/'preparation-code'/name)
with tarfile.open(D/'formal-audits-checkpoint.tar.gz','w:gz') as ar:
 ar.add(W/'all-audits',arcname='formal-audits');ar.add(W/'all-audits-complete.json',arcname='all-audits-complete.json')
start=datetime.datetime.fromisoformat(v['started_local']).timestamp()
with tarfile.open(D/'full-verify-attempt-001.tar.gz','w:gz') as ar:
 for name in ['full-verify.log','full-verify.log.json','full-verify.lease.log','full-verify-attempt.json','verify-resource-plan.json','verify-scheduling-telemetry.json']:
  ar.add(W/name,arcname=name)
 for p in (R/'.lake/verify').iterdir():
  if p.is_file() and p.stat().st_mtime>=start:ar.add(p,arcname='verify-interrupted/'+p.name)
with tarfile.open(D/'B4-tool-regression.tar.gz','w:gz') as ar:
 ar.add(W/'B4-tests-v4',arcname='B4-tests')
 for name in ['B4-regression-complete.json','B4-native-regression.log','B4-native-regression.log.json']:ar.add(W/name,arcname=name)
checkpoint={'complete':False,'passed_checks':16,'total_checks':17,'pending':['normal full verify'],'formal_audits_passed':106,'full_verify_attempt_001':v,'full_verify_progress':json.loads((R/'.lake/verify/audit-progress.json').read_text()),'source_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'next_run_policy':'Await explicit approval of one longer night bulk ticket. Keep no-cache full scope, maximum4jobs and32GB actual process memory; reserve scheduler headroom. No new ticket currently pending.','B4_regression_passed':True}
(D/'checkpoint-2026-11-15.json').write_text(json.dumps(checkpoint,ensure_ascii=False,indent=2))
p=R/'formalization-plans/stage-ii/bulk/report-bulk-w1.md';s=p.read_text();assert '## B3′ 正式監査通過・full verify中断（11-15 05時）' not in s
s+='''\n\n## B3′ 正式監査通過・full verify中断（11-15 05時）

一覧：済み 2／全体 22（うち追加 0）。全22項目の適用は済んでいるが、最終ゲートが残るため完了とはしない。

正式監査106本は全件成功（一本ずつ、通常のbulk鍵を監査ごとに返却）。[結果](bulk-b3prime/all-audits-complete.json)と[原記録](bulk-b3prime/formal-audits-checkpoint.tar.gz)を保存した。先行46本は既述の入力同一性の証跡により保持し、その元receiptを編集していない。保存比較29束・214本の未説明0、引用/タグ2,564組の欠落・余分0、root成功も維持している。

B4の補助手順は、共有の書換器を変更せず、宣言の実際の移動先のimportを資料側で補う。[README](bulk-b3prime/B4/README.md)とrewrite.py、移動した公開宣言の所有元1,606行（同名721行）を保存した。静的4ケース・header3ケースと、実Leanの失敗再現/補完後成功の2ケースが通った（[結果](bulk-b3prime/B4-regression-complete.json)、[原記録](bulk-b3prime/B4-tool-regression.tar.gz)）。分割された定義・削除wrapper・EInfinityにBS依存を戻すものは保留にする。他のレーンの作業木の変更0。

full verifyは`871516d78`でキャッシュを使わず4ジョブ・32GBで実行。rootと監査前提のbuildは成功したが、監査104／106の時点でプロセス合計RSSが32,190,054,400 bytesとなり、32GBの監視上限で中断した。04:29:26〜04:57:37、1,691秒。30分の上限の前に鍵を返している。[中断の全記録](bulk-b3prime/full-verify-attempt-001.tar.gz)を保存し、成功のsummaryを作っていない。古いverifyのsummaryを今回の成功として再利用していない。

[チェック表](bulk-b3prime/completion-audit.json)は16／17成功、残りはfull verifyだけ。直列のaxiom監査とsorry検査も含むため、完全実行は30分を超える見込みである。指示書§2の通常の30分上限を維持し、full verifyの再実行一回だけ夜の鍵を最長60分使う承認を依頼した。メモリ上限は増やさず、次回はスケジューラに余裕を持たせる。現在は鍵を持たず、次のverifyも要求していない。5∞-3a段0の紙の案は準備しているが、B3′完了報告ではない。
'''
p.write_text(s);print('Checkpoint saved without declaring B3prime complete')
