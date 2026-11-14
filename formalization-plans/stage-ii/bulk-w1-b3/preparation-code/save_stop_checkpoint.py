from pathlib import Path
import json,gzip,shutil,subprocess,datetime
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');d=r/'formalization-plans/stage-ii/bulk-w1-b3';d.mkdir(exist_ok=True)
assert json.load(open(w/'preservation-complete.json'))['modules']==10195
assert json.load(open(w/'declaration-table-summary.json'))['unmatched_authored']==0
assert json.load(open(w/'full-source-scope-check.json'))['status']=='PASS'
assert json.load(open(w/'target-build-coverage-check.json'))['status']=='PASS'
for name in ['frozen-main-change.json','target-build-complete.json','moved-audits-complete.json','preservation-complete.json','alias-check-complete.json','attribute-metadata-check.json','native-tag-metadata-check.json','baseline-section-edges.json','delta-collect-complete.json','delta-follow-complete.json','new-main-tiers.json','new-main-foundations.json','owned-private-rules-summary.json','target-build-coverage-check.json','declaration-table-summary.json','full-path-summary.json','full-source-scope-check.json','bs-section-order-check.json','base-math-scope-check.json','declaration-table-stop-check.log.json']:
 shutil.copy2(w/name,d/name)
for name in ['namespace-map.json','namespace-rewrite-map.json','module-map.json','preservation-module-plan.json','owned-comparison-name-map.json','delta-rewrite-status.json','static-layers.json','full-path-table.json','independent-delta-replay-check.json']:
 (d/(name+'.gz')).write_bytes(gzip.compress((w/name).read_bytes(),mtime=0))
for name in ['declaration-names.jsonl.gz','declaration-inventory-before.jsonl.gz','declaration-inventory-after.jsonl.gz','declaration-generated-groups.jsonl.gz','b4-branch-impact.json','B4-README.md']:shutil.copy2(w/name,d/name)
for p in w.glob('b4-*-files.json'):shutil.copy2(p,d/p.name)
resources=[]
for p in sorted(w.glob('preservation-slot-*.log.json')):
 obj=json.load(open(p));assert obj['rc']==0 and obj['reason'] is None;resources.append(obj)
(d/'preservation-resources.json').write_text(json.dumps(resources,ensure_ascii=False,indent=2))
code=d/'preparation-code';code.mkdir(exist_ok=True)
for p in w.glob('*.py'):shutil.copy2(p,code/p.name)
impact=json.load(open(w/'b4-branch-impact.json'))['branches'];decl=json.load(open(w/'declaration-table-summary.json'));change=json.load(open(w/'frozen-main-change.json'))
lines=['','### B3 全体保存比較完了・凍結mainの変更による停止（'+datetime.datetime.now().strftime('%m-%d %H:%M')+'）','','全10,195元モジュールの保存比較が成功し、未説明0。対象10,227本・前提込み29,776本の成功記録と現在のソース署名を再照合し一致した。全Lean作業木33,450本について、凍結before・承認済み束・採取済み増分からの期待値に対する欠落・余分・不一致0。Kerodonタグ前後672組、引用属性1,883組は欠落・余分0で、内容・版・場所の不整合0。互換90名・20包み、移した監査4本も成功済み。','','宣言名の全表は元モジュール10,195本を対象とし、ソース著者宣言の未対応0。compiler生成宣言は順番で対応を捏造せず、前後の実名の全在庫と比較群を別に保持する。件数は declaration-table-summary.json、実名は declaration-names.jsonl.gz と両側inventoryに保存した。','','後続のroot開始前の確認で、mainが凍結a9dc71e46から'+change['actual_main'][:9]+'へ進んだことを検出した。差分は formalization-plans/bhatt-scholze/bhatt-scholze-codex-w16.md の文書6行だけで、本体の変更はない。bulk-b3-goal.md §5(b) の停止条件に従い、基準を黙って更新せず、root・正式106監査・full verifyは開始していない。差分と検出時刻は frozen-main-change.json に保存した。保存比較の成功と後続ゲートの成功を混同しない。このコミットは完了報告ではない。','','承認済み範囲の移動の追加取り下げはない。IntegralExistenceは指定の元パスを維持。BSの逆向き34辺（直接参照31・import見せ直し3）を記録し、整理はB3′。厳密な節順序検査の15辺は凍結mainから存在し、両端ともB3で移動していない。免除を増やさず残件を明記した。層順序・実装境界・未解決import・循環0。','','B4資料はgit参照だけから更新した。下の「完全名一致」は静的な下限で、非修飾名の確定には原環境で全候補のcollectが必要。draftsを除外し、元HEAD・対象一覧・改名表と一行コマンドを添付した。','','| 枝 | 採取候補ファイル | 旧モジュール・完全名一致ファイル |','|---|---:|---:|']
for b,row in impact.items():lines.append('| '+b+' | '+str(row['collect_file_count'])+' | '+str(row['files_count'])+' |')
lines+=['','夜間処理の残りはroot・106正式監査・full verify。再開が認められた場合も32GiB・4ジョブ、全監査直列、verifyの大監査排他を保持する。共有鍵は使用していない。朝8時に残る重い処理を止める規則も維持する。','']
with (r/'formalization-plans/stage-ii/report-bulk-w1.md').open('a') as f:f.write('\n'.join(lines))
subprocess.run(['git','add','-A','--','SerrePositivity','SerrePositivity.lean','scripts','research','formalization-plans/stage-ii/bulk-w1-b3','formalization-plans/stage-ii/report-bulk-w1.md'],cwd=r,check=True)
subprocess.run(['git','commit','-q','-m','refactor(bulk): preserve frozen B3 layout and report main freeze interruption'],cwd=r,check=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();(w/'stopped-source-checkpoint.json').write_text(json.dumps({'head':head,'time':datetime.datetime.now().isoformat(),'reason':'frozen main changed; later gates not run','preservation_modules':10195},indent=2));print(head,flush=True)
