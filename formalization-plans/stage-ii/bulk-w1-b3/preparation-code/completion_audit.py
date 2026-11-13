"""Fail-closed evidence audit of the full B3 deliverable; never marks a goal complete."""
from pathlib import Path
import json,subprocess,hashlib
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');checks=[]
def record(name,ok,evidence):checks.append({'requirement':name,'proved':bool(ok),'evidence':evidence})
def load(name):
 p=w/name
 return json.load(open(p)) if p.exists() else None
base=load('baseline.json');head=subprocess.check_output(['git','rev-parse','main'],cwd=r,text=True).strip()
from check_frozen_main import check as check_frozen_main
try:
 compatibility=check_frozen_main();compatible=True
except AssertionError:
 compatibility=load('main-compatibility-check.json');compatible=False
record('Frozen mathematical main unchanged; authorized documents allowed',compatible,compatibility)
for name in ['base-math-scope-check.json','full-source-scope-check.json','independent-delta-replay-check.json','target-build-coverage-check.json','declaration-table-summary.json']:
 d=load(name)
 if name=='declaration-table-summary.json':ok=d is not None and d['unmatched_authored']==0 and d['source_modules']==10195
 else:ok=d is not None and d.get('status')=='PASS'
 record(name,ok,name)
d=load('target-build-complete.json');record('All targets and prerequisites built',d is not None and d['modules']==29776 and d['requested']==10227,'target-build-complete.json')
d=load('native-tag-metadata-check.json');record('Native Kerodon tags preserved without missing/extra',d is not None and all(x['expected']==x['actual']==672 and not x['missing'] and not x['extra'] for x in d.values()),'native-tag-metadata-check.json')
d=load('attribute-metadata-check.json');record('Citation entries/content/edition/source locations match',d is not None and d['expected']==d['actual']==1883 and not any(d[k] for k in ['missing','extra','different','metadata_errors']),'attribute-metadata-check.json')
d=load('alias-check-complete.json');record('Compatibility aliases including dates and duplicate attrs',d is not None and d['status']=='PASS' and d['aliases']==90 and d['wrappers']==20,'alias-check-complete.json')
d=load('preservation-complete.json');record('Full 10195 original-module preservation',d is not None and d['modules']==10195,'preservation-complete.json')
d=load('owned-private-rules-summary.json');record('Ordinary private ownership retained',d is not None and d['before_source_private_bindings']==11690 and d['after_source_private_bindings']==11700 and not d['missing_private_source_bindings'],'owned-private-rules-summary.json')
d=load('root-build-complete.json');record('Whole root lake build SerrePositivity',d is not None and d['rc']==0 and d['reason'] is None and d['command']==['lake','build','SerrePositivity'],'root-build-complete.json')
a=load('all-audit-inventory.json');d=load('all-audits-complete.json');manifest={x.strip() for x in (r/'scripts/refactor/audit_manifest.txt').read_text().splitlines() if x.strip() and not x.startswith('#')};expected={str(p.relative_to(r)) for p in (r/'scripts').glob('audit_*.lean')}|{str(p.relative_to(r)) for p in (r/'scripts/audit').rglob('*.lean')};record('Every formal audit executed successfully',a is not None and d is not None and set(a['audits'])==manifest==expected=={x['path'] for x in d['results']} and len(d['results'])==len(expected) and d['success']==len(expected) and not d['failed'] and all(x['rc']==0 and x['reason'] is None for x in d['results']),{'inventory':'all-audit-inventory.json','results':'all-audits-complete.json','current_discovered':len(expected)})
verify_path=r/'.lake/verify/summary.json';v=json.load(open(verify_path)) if verify_path.exists() else None;d=load('full-verify-complete.json');ok=d is not None and d['rc']==0 and d['reason'] is None and v is not None and v['status']=='PASS' and v['gate'] is True and not v['failures'] and v['audit_count']==v['executed_audit_count']==len(expected) and v['counts']['audit']['success']==len(expected) and all(x['failure']==x['known']==0 for x in v['counts'].values());record('Full uncached unrestricted verify gate',ok,str(verify_path))
runner=v.get('runner',{}) if v else {};scheduling=runner.get('scheduling',{});exclusive=set(json.load(open('/tmp/bulk-w1-b2/b3-heavy-audit-plan.json'))['VERIFY_EXCLUSIVE_AUDITS'].split())
record('Verify actual configuration 4 jobs / 32 GiB and large-audit exclusion',bool(runner) and runner.get('jobs')==4 and runner.get('cache_enabled') is False and scheduling.get('memory_budget_bytes')==32*1024**3 and exclusive<=set(scheduling.get('exclusive_audits',[])) and scheduling.get('max_exclusive_concurrent',2)<=1,{'runner':str(r/'.lake/verify/runner.json')})
if v:
 executed={x['name'] for x in v['stages'] if x['kind']=='audit'}
else:executed=set()
record('Verify executed exact formal audit set',v is not None and executed==expected and len([x for x in v['stages'] if x['kind']=='audit'])==len(expected),str(verify_path))
resources=[]
for path in (w/'target-build').glob('*.json'):
 if not path.name.endswith('.log.json'):resources.append(json.load(open(path))['resource'])
for name in ['root-build-complete.json','full-verify-complete.json']:
 if obj:=load(name):resources.append(obj)
if obj:=load('all-audits-complete.json'):resources.extend(obj['results'])
record('Successful heavy processes within 32 GiB and recorded job limits',bool(resources) and all(x['rc']==0 and x['reason'] is None and x['peak_process_tree_rss_bytes']<=32*1024**3 and x.get('peak_lean_or_snapshot_jobs',0)<=4 for x in resources),{'successful_resource_receipts':len(resources)})

retained='SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence';plan=load('module-map.json');proposed=json.load(open('/tmp/bulk-w1-b2/preservation-module-plan.json'))['modules'][retained];record('IntegralExistence retained at authorized original path',(r/(retained.replace('.','/')+'.lean')).is_file() and not (r/(proposed.replace('.','/')+'.lean')).exists() and plan.get(retained,retained)==retained,'module-map.json')
d=load('bs-section-order-check.json');record('Approved BS 34 paper reversals retained with actual refs',d is not None and d.get('edge_set_matches_approved') is True and len(d['paper_section_reverse_edges'])==34 and all('actual_compiler_reference_names' in e and 'approved_reason' in e for e in d['paper_section_reverse_edges']),'bs-section-order-check.json')
d=load('static-layers.json');b=load('baseline-section-edges.json');record('No tier/import/cycle violation or new reverse exception',d is not None and b is not None and len(d['violations'])==len(b)==15 and all(x['kind']=='reverse-section' for x in d['violations']) and all(x['exists_in_frozen_main'] and not x['source_moved_in_b3'] and not x['target_moved_in_b3'] for x in b),{'strict_result':'static-layers.json','unchanged_frozen_main_debt':'baseline-section-edges.json'})
checkpoint_path='verified-source-checkpoint.json' if (w/'verified-source-checkpoint.json').exists() else 'stopped-source-checkpoint.json'
d=load(checkpoint_path)
source_paths=['SerrePositivity','SerrePositivity.lean','scripts','research']
committed=False
if d is not None:
 checkpoint_exists=subprocess.run(['git','cat-file','-e',d['head']+'^{commit}'],cwd=r,capture_output=True).returncode==0
 ancestor=subprocess.run(['git','merge-base','--is-ancestor',d['head'],'HEAD'],cwd=r,capture_output=True).returncode==0
 checkpoint_same_sources=subprocess.run(['git','diff','--quiet',d['head'],'HEAD','--',*source_paths],cwd=r).returncode==0
 no_worktree_source_diff=not subprocess.check_output(['git','status','--porcelain','--',*source_paths],cwd=r,text=True).strip()
 committed=checkpoint_exists and ancestor and checkpoint_same_sources and no_worktree_source_diff
record('Preservation-checked source migration committed',committed,checkpoint_path)
impact=load('b4-branch-impact.json');branches={'math/inf-supply','math/inf-supply-b','math/bs-impl','math/scheme'};record('B4 all four branch-ref inventories and non-draft file lists',impact is not None and set(impact['branches'])==branches and all('head' in row and 'collect_files' in row and all(not p.startswith('formalization-plans/') and '/drafts/' not in p for p in row['collect_files']) for row in impact['branches'].values()),'b4-branch-impact.json')
record('B4 module and owned namespace maps plus one-line rewrite instructions',all((w/p).exists() for p in ['module-map.json','namespace-map.json','namespace-rewrite-map.json','B4-README.md','full-path-summary.json','declaration-names.jsonl.gz']),{'maps':['module-map.json','namespace-rewrite-map.json'],'instructions':'B4-README.md'})
summary={'status':'PASS' if all(x['proved'] for x in checks) else 'INCOMPLETE','checks':checks,'proved':sum(x['proved'] for x in checks),'requirements':len(checks)};(w/'completion-audit.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print(json.dumps({'status':summary['status'],'proved':summary['proved'],'requirements':len(checks),'unproved':[x['requirement'] for x in checks if not x['proved']]},ensure_ascii=False));raise SystemExit(summary['status']!='PASS')
