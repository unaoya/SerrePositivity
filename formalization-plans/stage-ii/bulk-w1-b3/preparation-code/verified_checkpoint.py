from pathlib import Path
import json,gzip,shutil,subprocess,datetime
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');d=r/'formalization-plans/stage-ii/bulk-w1-b3';base=json.load(open(w/'baseline.json'));assert subprocess.check_output(['git','rev-parse','main'],cwd=r,text=True).strip()==base['frozen_main']
for f in ['target-build-complete.json','moved-audits-complete.json','preservation-complete.json','alias-check-complete.json']:assert (w/f).exists(),f
a=json.load(open(w/'attribute-metadata-check.json'));assert not any(a[k] for k in ['missing','extra','different','metadata_errors'])
t=json.load(open(w/'native-tag-metadata-check.json'));assert all(not v['missing'] and not v['extra'] for v in t.values())
layer=json.load(open(w/'static-layers.json'));assert not any(v['kind']!='reverse-section' for v in layer['violations']),layer['violations'][:3]
subprocess.run(['python3','-B',str(w/'check_baseline_edges.py')],check=True);edges=json.load(open(w/'baseline-section-edges.json'));assert all(e['exists_in_frozen_main'] and not e['source_moved_in_b3'] and not e['target_moved_in_b3'] for e in edges)
subprocess.run(['python3','-B',str(w/'full_path_table.py')],check=True)
subprocess.run(['python3','-B',str(w/'make_declaration_table.py')],check=True)
for name in ['target-build-complete.json','moved-audits-complete.json','preservation-complete.json','alias-check-complete.json','attribute-metadata-check.json','native-tag-metadata-check.json','baseline-section-edges.json','delta-collect-complete.json','delta-follow-complete.json','new-main-tiers.json','new-main-foundations.json','owned-private-rules-summary.json','declaration-table-summary.json','full-path-summary.json']:
 shutil.copy2(w/name,d/name)
for name in ['namespace-map.json','namespace-rewrite-map.json','module-map.json','preservation-module-plan.json','owned-comparison-name-map.json','delta-rewrite-status.json','static-layers.json','full-path-table.json']:
 (d/(name+'.gz')).write_bytes(gzip.compress((w/name).read_bytes(),mtime=0))

for name in ['declaration-names.jsonl.gz','declaration-inventory-before.jsonl.gz','declaration-inventory-after.jsonl.gz','declaration-generated-groups.jsonl.gz']:shutil.copy2(w/name,d/name)
subprocess.run(['python3','-B',str(w/'branch_impact.py')],check=True)
shutil.copy2(w/'b4-branch-impact.json',d/'b4-branch-impact.json')
for f in w.glob('b4-*-files.json'):shutil.copy2(f,d/f.name)
shutil.copy2(w/'B4-README.md',d/'B4-README.md')
code=d/'preparation-code'
for p in w.glob('*.py'):shutil.copy2(p,code/p.name)
report=r/'formalization-plans/stage-ii/report-bulk-w1.md';counts=json.load(open(w/'target-build-complete.json'));pres=json.load(open(w/'preservation-complete.json'))
with report.open('a') as f:f.write('\n### B3 対象と全体保存比較のチェックポイント（'+datetime.datetime.now().strftime('%m-%d %H:%M')+'）\n\n凍結基準の増分686本の採取・書き換えが完了し、保留0。対象ビルドと前提'+str(counts['modules'])+'本が成功。元'+str(pres['modules'])+'モジュールの全体保存比較が成功し、未説明0。既存Kerodonタグは前後各'+str(t['after']['actual'])+'組で欠落・余分0、引用属性'+str(a['actual'])+'組で欠落・余分・内容・場所の不整合0。互換90名と移した監査4本も成功した。これはroot・全監査・full verifyの完了報告ではない。\n\n新しいファイルの5段の層を依存順に確定した。既存の明示的な層・免除は変更していない。DGなどの実装や入口を消費する新規ファイルはConsumers、独立した基盤の新規前提はSharedFoundationとし、Comparisonから実装への例外を増やさない。層の順序・実装境界の違反0。節の逆向きは凍結main由来の'+str(len(edges))+'辺を厳密検査の残件として保持し、0件と呼ばない。両端はB3で移動しておらず、B3′での確認対象として付表を残した。\n\nここから、同じ枝でroot、全監査、VERIFY_JOBS=4・VERIFY_MEMORY_GB=32のfull verifyへ進む。大きい監査は同時に二本流さず、朝8時に重い処理を終了する。共有鍵は使用しない。\n')
subprocess.run(['git','add','-A','--','SerrePositivity','SerrePositivity.lean','scripts','research','formalization-plans/stage-ii/bulk-w1-b3','formalization-plans/stage-ii/report-bulk-w1.md'],cwd=r,check=True)
subprocess.run(['git','commit','-q','-m','refactor(bulk): apply frozen-main B3 layout with preserved declarations'],cwd=r,check=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();(w/'verified-source-checkpoint.json').write_text(json.dumps({'head':head,'frozen_main':base['frozen_main'],'time':datetime.datetime.now().isoformat()},indent=2));print('Committed verified source checkpoint',head,flush=True)
