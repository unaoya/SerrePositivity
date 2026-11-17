"""Publish observed first-night state, without starting or relaxing any gate."""
from pathlib import Path
import json,shutil,subprocess,datetime,tarfile,gzip
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'evidence/bulk/bulk-w1-b3'
def load(name):
 p=W/name;return json.load(open(p)) if p.exists() else None
from check_frozen_main import check
check()
subprocess.run(['python3','-B',str(W/'branch_impact.py')],check=True)
subprocess.run(['python3','-B',str(W/'completion_audit.py')])
root=load('root-build-complete.json');audits=load('all-audits-progress.json') or [];verify=load('full-verify-complete.json');passed=[a for a in audits if a['rc']==0 and a['reason'] is None];failed=[a for a in audits if a['rc']!=0 and a['reason'] not in ['daytime boundary']];interrupted=[a for a in audits if a['reason']=='daytime boundary'];inventory=load('all-audit-inventory.json');count=inventory['count'] if inventory else 106
for name in ['main-compatibility-check.json','live-budget-watch.json','root-build-complete.json','root-build.log.json','all-audit-prerequisites.log.json','full-verify.log.json','all-audit-inventory.json','all-audits-progress.json','all-audits-results.json','all-audits-complete.json','full-verify-complete.json','completion-audit.json','b4-branch-impact.json']:
 if (W/name).exists():shutil.copy2(W/name,D/name)
for p in W.glob('b4-*-files.json'):shutil.copy2(p,D/p.name)
for p in W.glob('*.py'):shutil.copy2(p,D/'preparation-code'/p.name)
receipts=[]
for p in sorted((W/'all-audits').glob('*.log.json')):
 obj=json.load(open(p));receipts.append({'receipt':str(p.relative_to(W)),**obj})
(D/'first-night-audit-resources.json').write_text(json.dumps(receipts,ensure_ascii=False,indent=2))
with tarfile.open(D/'first-night-audit-logs.tar.gz','w:gz') as archive:
 for p in sorted((W/'all-audits').glob('*')):
  if p.is_file():archive.add(p,arcname='all-audits/'+p.name)
if (W/'all-audit-prerequisites.log').exists():(D/'all-audit-prerequisites.log.gz').write_bytes(gzip.compress((W/'all-audit-prerequisites.log').read_bytes(),mtime=0))
status={'recorded_at':datetime.datetime.now().isoformat(),'root_success':bool(root and root['rc']==0 and root['reason'] is None),'formal_audits_total':count,'formal_audits_success':len(passed),'formal_audits_failed':len(failed),'formal_audits_daytime_interrupted':[x['path'] for x in interrupted],'formal_audits_remaining':count-len(passed),'full_verify_success':bool(verify and verify['rc']==0 and verify['reason'] is None),'preservation_modules':10195,'preservation_unexplained':0,'additional_withdrawals':[],'baseline_mathematical_main':'c5c4436c0'}
(D/'first-night-status.json').write_text(json.dumps(status,ensure_ascii=False,indent=2))
lines=['','### B3 一晩目の報告（'+datetime.datetime.now().strftime('%m-%d %H:%M')+'）','','基準c5c4436c0の数学を保持し、増分686本の採取・再構成・参照書き換え、承認済み移動・属性・層の設定を適用した。対象10,227本と前提込み29,776本のビルドが成功。保存比較10,195元モジュール、未説明0。タグ672組、引用属性1,883組で欠落・余分0、引用の内容・版・場所も一致。互換90名・20包み、移した監査4本が成功。元宣言140,687記録の全表と前後実名の在庫を保存し、著者宣言の未対応0。','','root: '+('成功（実行時間'+str(round(root['seconds'],1))+'秒、ピークRSS '+str(root['peak_process_tree_rss_bytes'])+'バイト）' if status['root_success'] else '未完了')+'。正式監査: '+str(len(passed))+'/'+str(count)+'本が成功、実エラー'+str(len(failed))+'本、昼境界による中断'+str(len(interrupted))+'本。full verify: '+('成功' if status['full_verify_success'] else '未完了')+'。個別の成功・失敗・中断は付表に分け、昼境界の中断を成功へ数えていない。','', '追加の移動取り下げは0。IntegralExistenceの元パス維持など承認済みの狭い範囲を守った。BS逆向き34辺（直接31・見せ直し3）と、B3で両端を動かしていない凍結由来の節順序15辺は一覧に残し、B3′で確認する。層の順序・実装境界・未解決import・循環0。','','main文書更新を検出して一時停止したが、調整役の回答を受け、文書のみの更新を許容して07時台に再開した。本体・道具・設定の変更は許容しない。共有鍵は使用せず、32GB・4ジョブ、監査直列の制限で実行した。朝8時以降は軽い処理2ジョブまでとし、全監査・verifyは停止する。','','二晩目の残りは正式監査'+str(count-len(passed))+'本とfull verify'+('、rootの残り' if not status['root_success'] else '')+'。未実行分の時間はまだ実測できないため、完了見込みの時間は確約しない。夜23時から、実行対象とソース署名を照合して残るゲートへ進む。数学・比較の条件を変えて通すことはしない。','','B4の改名表・一行コマンド・4枝の影響一覧を最新git参照だけから更新した。草稿は採取候補に含めず、完全名の文字列一致を非修飾名まで含む確定件数と見なしていない。取り込みは調整役が行う。','']
with (R/'formalization-plans/stage-ii/bulk/report-bulk-w1.md').open('a') as f:f.write('\n'.join(lines))
subprocess.run(['git','add','--','evidence/bulk/bulk-w1-b3','formalization-plans/stage-ii/bulk/report-bulk-w1.md'],cwd=R,check=True)
subprocess.run(['git','commit','-q','-m','docs(bulk): report first B3 night and remaining final gates'],cwd=R,check=True)
print(json.dumps(status,ensure_ascii=False));print(subprocess.check_output(['git','rev-parse','--short','HEAD'],cwd=R,text=True).strip())
