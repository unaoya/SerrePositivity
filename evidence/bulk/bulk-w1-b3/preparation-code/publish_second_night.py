"""Save the observed second-night result; never changes mathematics or goal state."""
from pathlib import Path
import json,shutil,subprocess,datetime,tarfile,gzip
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'evidence/bulk/bulk-w1-b3'
def load(n):
 p=W/n;return json.load(open(p)) if p.exists() else None
subprocess.run(['python3','-B',str(W/'branch_impact.py')],check=True)
audit_rc=subprocess.run(['python3','-B',str(W/'completion_audit.py')]).returncode
from check_frozen_main import check
check()
source_head=load('verified-source-checkpoint.json')['head']
subprocess.run(['git','diff','--exit-code',source_head,'HEAD','--','SerrePositivity','SerrePositivity.lean','scripts','research','lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain'],cwd=R,check=True,stdout=subprocess.DEVNULL)
assert not subprocess.check_output(['git','status','--porcelain','--','SerrePositivity','SerrePositivity.lean','scripts','research','lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain'],cwd=R,text=True).strip()
for name in ['root-build-complete.json','all-audit-inventory.json','all-audits-progress.json','all-audits-results.json','all-audits-complete.json','full-verify-complete.json','main-compatibility-check.json','completion-audit.json','verify-resource-plan.json','second-night-budget-watch.json','second-night-worker-status.json','b4-branch-impact.json']:
 if (W/name).exists():shutil.copy2(W/name,D/name)
for p in W.glob('b4-*-files.json'):shutil.copy2(p,D/p.name)
for p in W.glob('*.py'):shutil.copy2(p,D/'preparation-code'/p.name)
with tarfile.open(D/'second-night-audit-logs.tar.gz','w:gz') as archive:
 for p in sorted((W/'all-audits').glob('*')):
  if p.is_file():archive.add(p,arcname='all-audits/'+p.name)
for name in ['root-build.log','all-audit-prerequisites.log','full-verify.log','second-night.log']:
 if (W/name).exists():(D/(name+'.gz')).write_bytes(gzip.compress((W/name).read_bytes(),mtime=0))
verify=R/'.lake/verify'
if (W/'full-verify-complete.json').exists():
 with tarfile.open(D/'full-verify-records.tar.gz','w:gz') as archive:
  for name in ['summary.json','runner.json','audit-progress.json','preparation.json','stage.tsv','events.jsonl']:
   if (verify/name).is_file():archive.add(verify/name,arcname='verify/'+name)
 summary=json.load(open(verify/'summary.json'));(D/'full-verify-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2))
root=load('root-build-complete.json');a=load('all-audits-complete.json');p=load('all-audits-progress.json') or [];done=sum(x['rc']==0 and x['reason'] is None for x in p);v=load('full-verify-complete.json');c=load('completion-audit.json');worker=load('second-night-worker-status.json') or {};ready=audit_rc==0 and c['status']=='PASS' and worker.get('rc')==0
lines=['','### B3 二晩目の検査結果（'+datetime.datetime.now().strftime('%m-%d %H:%M')+'）','','数学の基準はc5c4436c0、移動・参照書き換え・属性付与は保存比較済みの本体から変更していない。二晩目の開始前に対象成功記録・全ソース・増分独立再構成・全宣言表の署名を再検査した。mainの文書以外の増分は許容しない。','','root: '+('成功' if root and root['rc']==0 and root['reason'] is None else '未完了')+'。正式全監査: '+str(done)+'/106本成功。full verify: '+('成功' if v and v['rc']==0 and v['reason'] is None else '未完了')+'。完了要件照合: '+str(c['proved'])+'/'+str(c['requirements'])+'項目。未証明を成功扱いにしない。','','保存比較10,195元モジュール・未説明0、タグ672組・引用1,883組の欠落余分0、互換90名・20包み、移動監査4本の成功を保持した。IntegralExistenceは元パス、BS逆向き34辺は一覧だけ、凍結由来の未移動15辺は免除せずB3′の残件として保持した。','','verifyは4ジョブ・32GB、キャッシュなし・全対象の正式ゲートで実行する。既存の大監査の排他群へ実測10GB以上の監査も加え、主定理監査は既存ランナーどおり並列プールの後に単独実行する。共有鍵は使っていない。','','B4の通常import表・所有元付き実名表・書き換え用表・一行コマンド・4枝の影響一覧を最新git参照に更新した。他レーンの作業木は変更していない。','','全要件の機械照合が成功し、取り込み前の最終確認ができる状態。mainへの取り込みは調整役が行う。' if ready else '残る要件はcompletion-audit.jsonに列挙した。これは完了報告ではない。','']
with (R/'formalization-plans/stage-ii/bulk/report-bulk-w1.md').open('a') as f:f.write('\n'.join(lines))
subprocess.run(['git','add','--','evidence/bulk/bulk-w1-b3','formalization-plans/stage-ii/bulk/report-bulk-w1.md'],cwd=R,check=True)
subprocess.run(['git','commit','-q','-m','docs(bulk): publish observed second-night gates and follow-up tables'],cwd=R,check=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();(W/'second-night-published.json').write_text(json.dumps({'head':head,'all_requirements_proved':ready,'time':datetime.datetime.now().isoformat()},indent=2));print('Published',head,'all requirements proved',ready,flush=True)
