from pathlib import Path
import json,gzip,hashlib,subprocess
r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');d=r/'evidence/bulk/bulk-b3prime';f=r/'evidence/bulk/bulk-5inf3a'
load=lambda p:json.loads(p.read_text())
c=load(d/'completion-audit.json');v=load(d/'full-verify-complete.json');p=load(f/'stage0-provenance.json');i=load(f/'existing-api-inventory.json')
assert c['all_passed'] and c['passed']==c['total_checks']==17 and c['scope_complete']==22
raw=gzip.decompress((d/'full-verify-summary.json.gz').read_bytes());assert hashlib.sha256(raw).hexdigest()==v['full_summary_sha256'];s=json.loads(raw)
assert s['gate'] and s['status']=='PASS' and not s['failures'] and s['counts']['audit']=={'success':106,'failure':0,'known':0}
assert s['counts']['build']=={'success':2,'failure':0,'known':0} and s['counts']['sorry']=={'success':1,'failure':0,'known':0}
assert s['runner']['jobs']==3 and s['runner']['cache_enabled'] is False and s['runner']['scheduling']['memory_budget_bytes']==24000000000
assert len(s['runner']['stages'])==107 and all(row['cached'] is False for row in s['runner']['stages'])
assert s['runner']['scheduling']['max_concurrent']<=3 and s['runner']['scheduling']['max_exclusive_concurrent']<=1
assert v['shared_key'] is False and v['time_limit_seconds'] is None
assert not subprocess.check_output(['git','diff',v['head'],'HEAD','--name-only','--','SerrePositivity','SerrePositivity.lean','scripts','lakefile.toml','lake-manifest.json','lean-toolchain','research/bibliography.json','formalization-plans/bhatt-scholze/drafts'],cwd=r,text=True).strip()
assert not subprocess.check_output(['git','status','--porcelain'],cwd=r,text=True).strip()
assert p['implemented_lean_declarations']==0 and p['source_tree']==i['source_tree']==subprocess.check_output(['git','rev-parse','HEAD:SerrePositivity'],cwd=r,text=True).strip()
assert len(i['items'])==13
for row in i['items']:assert hashlib.sha256((r/row['path']).read_bytes()).hexdigest()==row['source_sha256']
report=(r/'formalization-plans/stage-ii/bulk/report-bulk-w1.md').read_text();assert '## B3′ 完了報告（' in report and '## 5∞-3a 段0：' in report
assert report.index('## B3′ 完了報告（')<report.index('## 5∞-3a 段0：')
assert load(d/'scope-items-complete.json')['final_complete']==22
b4=load(d/'B4-regression-complete.json');assert b4['passed']
assert hashlib.sha256((d/'B4/rewrite.py').read_bytes()).hexdigest()==b4['script_sha256']
assert hashlib.sha256((d/'B4/declaration-import-owners.json').read_bytes()).hexdigest()==b4['ownership_sha256']
for path in ['B4/README.md','B4/rewrite.py','B4/module-map.json','B4/namespace-rewrite-map.json','B4/declaration-import-owners.json','B4-tool-regression.tar.gz','formal-audits-and-full-verify.tar.gz','actual-preservation-v3b.tar.gz']:
 assert (d/path).is_file(),path
print('CLOSING AUDIT PASS: B3prime22items/all17gates/full106audit+sorry+2build, unchanged verified sources, committed B4,5inf3a stage0 paper and13API inventory. Main integration remains coordinator-owned.')
