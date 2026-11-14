"""Publish only fully proved B3 results; no mathematics or goal state is modified."""
from pathlib import Path
import json,subprocess,shutil,tarfile,gzip,datetime,hashlib
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'formalization-plans/stage-ii/bulk-w1-b3';V=R/'.lake/verify'
def load(p):return json.load(open(p))
from check_frozen_main import check
check()
for n in ['check_source_scope.py','check_target_coverage.py','independent_delta_replay.py','approved_scope_audit.py','branch_impact.py','completion_audit.py']:subprocess.run(['python3','-B',str(W/n)],check=True)
c=load(W/'completion-audit.json');assert c['status']=='PASS' and c['proved']==c['requirements']
v=load(V/'summary.json');receipt=load(W/'full-verify-complete.json');assert receipt['rc']==0 and receipt['reason'] is None and v['status']=='PASS' and v['gate'] is True and not v['failures'] and v['executed_audit_count']==v['audit_count']==106
assert len([x for x in v['stages'] if x['kind']=='audit'])==106 and all(not x.get('cached',False) and x['exit_code']==0 for x in v['stages'])
cp=load(W/'verified-source-checkpoint.json');critical=['SerrePositivity','SerrePositivity.lean','scripts','research','lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain'];subprocess.run(['git','diff','--exit-code',cp['head'],'HEAD','--',*critical],cwd=R,check=True,stdout=subprocess.DEVNULL);assert not subprocess.check_output(['git','status','--porcelain','--',*critical],cwd=R,text=True).strip()
verify_commit=v['commit'];subprocess.run(['git','diff','--exit-code',verify_commit,'HEAD','--',*critical],cwd=R,check=True,stdout=subprocess.DEVNULL)
for name in ['all-audits-complete.json','all-audits-results.json','all-audits-progress.json','all-audits-first-pass-results.json','audit-corrected-reruns.json','verified-source-checkpoint.json','day-budget-watch.json','audit-rerun-aggregate-budget.json','full-verify-aggregate-budget.json','full-verify-complete.json','full-source-scope-check.json','target-build-coverage-check.json','approved-scope-audit.json','completion-audit.json','verify-resource-plan.json','main-compatibility-check.json','b4-branch-impact.json']:
 if (W/name).exists():shutil.copy2(W/name,D/name)
for p in W.glob('b4-*-files.json'):shutil.copy2(p,D/p.name)
shutil.copy2(W/'B4-README.md',D/'B4-README.md')
(D/'full-verify-summary.json').write_text(json.dumps(v,ensure_ascii=False,indent=2))
# Archive only records and output files named by this completed run, not stale logs.
current={V/n for n in ['summary.json','runner.json','stages.tsv','preparation.json','audit-progress.json','audits.txt','audit_targets.txt','layers.json','layers-exit-code.txt'] if (V/n).is_file()}
for row in v['stages']:
 for item in [row,*row.get('attempts',[])]:
  for key in ['log','time_log']:
   if item.get(key):
    p=(R/item[key]).resolve();assert p.is_relative_to(V.resolve());assert p.is_file();current.add(p)
with tarfile.open(D/'full-verify-current-run.tar.gz','w:gz') as archive:
 for p in sorted(current):archive.add(p,arcname='verify/'+str(p.relative_to(V)))
for n in ['full-verify.log','full-verify.log.json','audit-einfinity-corrected-rerun.log','audit-einfinity-corrected-rerun.log.json']:
 if (W/n).is_file():(D/(n+'.gz')).write_bytes(gzip.compress((W/n).read_bytes(),mtime=0))
index=[]
for i,row in enumerate(load(W/'all-audits-complete.json')['results']):
 log=W/'audit-einfinity-corrected-rerun.log' if row.get('replaces_initial_failure') else W/'all-audits'/f'{i:03}.log'
 index.append({'audit':row['path'],'accepted_log':str(log.relative_to(W)),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'rc':row['rc'],'seconds':row['seconds'],'peak_rss_bytes':row['peak_process_tree_rss_bytes']})
(D/'formal-audit-log-index.json').write_text(json.dumps(index,ensure_ascii=False,indent=2))
retained={'additional_withdrawn_moves':[],'specified_retentions':[{'path':'SerrePositivity/BhattScholze/Perfectoidization/Derived/IntegralExistence.lean','reason':'Explicit §2(3) instruction; split before moving in B3-prime'},{'module':'BhattScholze/Prismatic/Crystalline/Comparison/PDCechFrameHomotopy','reason':'PD-specific cochainHomotopy stays BS; generic algebraModule/index helpers extracted'},{'paths':['KST/Spectra/CoherentNerve','KST/LocalizingInvariants/SpectrumHomotopyFunctor'],'reason':'R83 deferred; approved scope avoids a 103-module expansion'}],'approved_literature_exception':'Kerodon 7.4 -> 9.3 retained, reason marked approved','baseline_debt':{'bs_paper_reverse_edges':34,'bs_direct_references':31,'bs_public_import_visibility_only':3,'strict_section_reverse_edges':15,'strict_section_edges_both_endpoints_unmoved_in_B3':True},'excluded_scope':['Broad R21 9913-block proposal','Later B3-prime ledger sections 7/8/10 changes','Unused-declaration deletion']};(D/'retained-and-deferred.json').write_text(json.dumps(retained,ensure_ascii=False,indent=2))
# The compiled inspection source and its original/source/binary SHA receipts are preserved for reproduction.
snap=Path('/tmp/bulk-w1-b2/private-snapshot')
with tarfile.open(D/'preservation-snapshot-source.tar.gz','w:gz') as archive:
 for n in ['Snapshot.lean','receipt.json']:
  if (snap/n).is_file():archive.add(snap/n,arcname=n)
for p in W.glob('*.py'):shutil.copy2(p,D/'preparation-code'/p.name)
impact=load(W/'b4-branch-impact.json')['branches'];jobs=v['runner']['jobs'];memory=v['runner']['scheduling']['memory_budget_bytes'];peak=receipt['peak_process_tree_rss_bytes']
readme=['# B3 検収用資料','','数学基準 `c5c4436c0`。B2検収済み範囲を新しいmainの増分へ再構成して適用した。文書だけのmain更新は許容し、ビルド入力の変更は停止する。','','| 検査 | 結果 |','|---|---|','| 対象と前提 | 10,227対象・前提込み29,776本、全件成功 |','| root | 31,251ジョブ成功。full verify内でも再実行成功 |','| 正式監査 | 106/106成功。E∞の引用名2件を訂正し当該監査を再実行 |','| full verify | 正式ゲートPASS、監査106本をキャッシュなしで再実行 |','| 保存比較 | 元10,195モジュール、未説明0 |','| 属性・タグ | 引用1,883組・Kerodon672組、欠落・余分0 |','| 宣言名 | 前140,687・後140,705記録、著者宣言の未対応0 |','| 互換 | 90名・20包み、二重instance/simpなし |','','## 主な資料','','- `full-verify-summary.json`・`full-verify-current-run.tar.gz`：現在の正式verifyの集計と、その実行が参照するログだけ。','- `all-audits-complete.json`・`formal-audit-log-index.json`：正式監査106本の受理した実行。','- `formal-audits-complete-logs.tar.gz`：初回と訂正後E∞のログ。初回失敗の履歴は残す。','- `preservation-evidence.tar.gz`：178組の比較receipt・結果・前後356snapshotの検証済みSHA。','- `preservation-snapshot-source.tar.gz`：検査用実行ソースと元ソース・実行ソース・binaryのSHA。','- `declaration-names.jsonl.gz`・`declaration-inventory-{before,after}.jsonl.gz`：所有元付き実名と完全な索引。compiler-onlyを順番で対応させない。','- `full-path-table.json.gz`：元パスから新パス・分割先への全表。','- `retained-and-deferred.json`：追加取り下げ0、指定維持、B3′へ残す既存の辺と範囲。','- `completion-audit.json`・`approved-scope-audit.json`：全要件と具体的な承認内容の照合。','- `B4-README.md`：元環境での採取・一行のrewriteコマンド・引用名の扱い。','- `b4-branch-impact.json`・`b4-*-files.json`：4枝のgit参照だけに基づく対象一覧。','- `module-map.json.gz`・`namespace-rewrite-map.json.gz`・`namespace-map.json.gz`：通常import・書き換え用実名・恒等6メソッドを含む全名表。','','## 残す既存事項','','層の順序・実装境界・欠落import・循環0。厳密な節順序の15辺は凍結mainから存在し、両端ともB3で移動していない。BSの論文順逆向き34辺（直接31・見せ直し3）は承認どおり一覧のみ。免除を増やさずB3′で確認する。Kerodon7.4→9.3の1辺は明示的な承認済み例外。','','mainへの取り込みは調整役が行う。B4は取り込み前の原環境で参照を採取し、枝のHEADが一覧から進んでいれば対象を更新する。','']
(D/'README.md').write_text('\n'.join(readme))
lines=['','## B3 完了報告（'+datetime.datetime.now().strftime('%m-%d %H:%M')+'）','','数学基準はc5c4436c0、検証対象のLean・実行スクリプトはfull verify開始時の4547afc5eから同一。B2検収済み範囲と増分686本の再構成を完了した。未承認の数学の主張・証明・界面の変更はない。[検収用資料](bulk-w1-b3/README.md)を結果の索引とする。','','| 検査 | 完了結果 |','|---|---|','| 対象ビルド | 10,227/10,227、前提込み29,776/29,776成功 |','| root | 31,251ジョブ成功、verify内の再ビルドも成功 |','| 正式全監査 | 106/106成功。BS段階II18,156宣言・AlgebraicGeometry8,615宣言を含む |','| full verify | PASS・gate=true、監査106本・失敗0・既知失敗0・監査結果キャッシュ0 |','| 全体保存比較 | 元10,195モジュール、未説明0。通常のprivateと互換の厳しい項構造比較を維持 |','| 引用・タグ | 引用1,883組、既存Kerodon672組。欠落・余分・内容・版・場所の不整合0 |','| 互換・移動監査 | 90名・20包み、移した監査4本が成功 |','','正式verifyの実設定は'+str(jobs)+'ジョブ・'+str(memory//1_000_000_000)+'GB、VERIFY_CACHE=0。全監査集合とsorry閉包を制限せず実行した。実行時間'+str(round(v['seconds'],3))+'秒、全子孫RSSピーク'+str(peak)+'バイト。大監査の排他も実行記録から確認した。共有の鍵は使用していない。E∞監査の初回失敗はモジュール名と宣言名の混同2件であり、実名へ訂正して監査を最初から再実行し成功した。初回の失敗と成功した再実行の両方を保存し、検査項目や公理の条件を減らしていない。','','追加取り下げは0。IntegralExistenceは指定の元パスに残し、PD固有のcochainHomotopyもBSに残した。Spectrum二入口は承認どおりR83へ。広いR21・B3′の追加範囲・未使用宣言の削除は入れていない。BSの逆向き34辺と凍結由来の未移動15辺は[維持・保留の一覧](bulk-w1-b3/retained-and-deferred.json)へ記録した。層・実装境界・欠落import・循環0、節順序の全てを前向きにしたとは主張しない。','','B4用のimport表・所有元付き実名表・一行rewriteコマンド・各枝の影響一覧を更新した。下表の一致数は完全名・旧モジュール名の静的な下限であり、非修飾名は全採取候補の原環境collectで確定する。draftsは除外。他レーンの作業木は変更していない。','','| 枝 | 観測HEAD | 採取候補 | 文字列一致ファイル |','|---|---|---:|---:|']
for branch,row in impact.items():lines.append('| '+branch+' | '+row['head'][:9]+' | '+str(row['collect_file_count'])+' | '+str(row['files_count'])+' |')
oversize=[event for event in v['runner']['scheduling'].get('events',[]) if event.get('oversize_alone')]
aggregate=load(W/'full-verify-aggregate-budget.json')
lines+=['','資源設定の注意：VERIFY_MEMORY_GB='+str(memory//1_000_000_000)+'はランナーの見積り予算であり、物理RSSの強制上限ではない。今回は'+str(len(oversize))+'件（F1）の見積りが予算を超え、既存ランナーのoversize_aloneで単独実行された。F1単体の実測最大RSSは30,218,108,928バイト、自レーン全体の監視ピークは'+str(aggregate['peak_process_tree_rss_bytes'])+'バイト（約31.1GB）。全体の32,000,000,000バイト強制上限内で完了し、監査の省略や大監査二本の同時実行はない。']
lines+=['','B4の具体的な一行コマンドと展開するJSONは[B4手順](bulk-w1-b3/B4-README.md)に記載した。全パス・実名・静的検査・原典の書誌確認と187件台帳の履歴も保存している。mainへの取り込みは調整役に委ねる。','']
with (R/'formalization-plans/stage-ii/report-bulk-w1.md').open('a') as stream:stream.write('\n'.join(lines))
subprocess.run(['git','add','--','formalization-plans/stage-ii/bulk-w1-b3','formalization-plans/stage-ii/report-bulk-w1.md'],cwd=R,check=True);subprocess.run(['git','commit','-q','-m','docs(bulk): complete B3 with full verify and B4 follow-up package'],cwd=R,check=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();(W/'final-publication.json').write_text(json.dumps({'head':head,'source_checkpoint':cp['head'],'verify_summary_commit':verify_commit,'requirements_proved':c['requirements'],'time':datetime.datetime.now().isoformat()},indent=2));print('Published fully proved B3',head,flush=True)
