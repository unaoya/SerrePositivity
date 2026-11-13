from pathlib import Path
import json,sys,subprocess,hashlib
from graphlib import TopologicalSorter,CycleError
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');old=Path('/tmp/bulk-w1-b2');sys.path.insert(0,str(r/'scripts/refactor'))
from layer_check import imports,under
from klw1_layer_check import check
cfg=json.load(open(r/'scripts/refactor/layers.json'))['klw1']
cache_file=w/'import-cache.json';cache=json.load(open(cache_file)) if cache_file.exists() else {};updated_cache={}
tracked=subprocess.check_output(['git','ls-files','-co','--exclude-standard','-z','--','*.lean'],cwd=r).decode().split('\0');graph={}
for rel in sorted(set(tracked)):
 if not rel or not (r/rel).is_file():continue
 m=rel[:-5].replace('/','.')
 stat=(r/rel).stat();stamp=[stat.st_mtime_ns,stat.st_size];entry=cache.get(rel)
 if entry and entry['stamp']==stamp:deps=entry['imports']
 else:deps=sorted(imports((r/rel).read_text()))
 updated_cache[rel]={'stamp':stamp,'imports':deps};graph[m]=set(deps)
cache_file.write_text(json.dumps(updated_cache))
missing=sorted(m for m in graph if under(m,'SerrePositivity.InfinityCategories') and m not in cfg['modules'])
(w/'new-unclassified-modules.json').write_text(json.dumps(missing,indent=2))
order=list(TopologicalSorter({m:deps&graph.keys() for m,deps in graph.items()}).static_order())
# Lower only mathematically independent prerequisite closure, matching B2's
# foundation treatment. No prior explicit tier or implementation boundary changes.
needed=set();todo=list(missing)
while todo:
 m=todo.pop()
 for dep in graph[m]&graph.keys():
  if dep not in needed:needed.add(dep);todo.append(dep)
blocked={};new_foundations={}
for m in order:
 blocked[m]=(under(m,'SerrePositivity.InfinityCategories') or under(m,'SerrePositivity.BhattScholze') or any(under(m,p) for p in cfg['implementation_prefixes']) or any(blocked[d] for d in graph[m]&graph.keys()))
 if m in needed and m.startswith('SerrePositivity.') and m not in cfg['modules'] and not blocked[m] and not under(m,'SerrePositivity.Archive'):
  cfg['modules'][m]='SharedFoundation';new_foundations[m]='prerequisite closure of newly classified IC modules, with no IC, BS, or implementation dependency'
(w/'new-main-foundations.json').write_text(json.dumps(new_foundations,indent=2))
new_tiers={}
for m in order:
 if m not in missing:continue
 deps={cfg['modules'].get(dep,'Consumers') for dep in graph[m] if dep in graph}
 tier='Consumers' if deps&{'Entrypoints','Consumers'} or any(any(under(dep,p) for p in cfg['implementation_prefixes']) for dep in graph[m]) else 'Comparison' if 'Comparison' in deps else 'Portable'
 cfg['modules'][m]=tier;new_tiers[m]={'tier':tier,'dependency_tiers':sorted(deps),'rule':'five per-file tiers in dependency order; independent IC files Portable, dependencies on Comparison stay Comparison, actual consumers of implementation or Entrypoints remain Consumers; no existing tier or exception changed'}
(w/'new-main-tiers.json').write_text(json.dumps(new_tiers,indent=2))
(w/'candidate-layers.json').write_text(json.dumps({'klw1':cfg},indent=2))
active={m:ds for m,ds in graph.items() if not any(under(m,p) for p in cfg['exclude_prefixes'])};report=check(active,cfg);(w/'static-layers.json').write_text(json.dumps(report,ensure_ascii=False,indent=2));print('layers',len(report['violations']),len(graph))
if not any(v['kind']!='reverse-section' for v in report['violations']):
 full=json.load(open(r/'scripts/refactor/layers.json'));full['klw1']=cfg
 (r/'scripts/refactor/layers.json').write_text(json.dumps(full,ensure_ascii=False,indent=2)+'\n')
 print('Applied exact per-file tiers; no exception added',len(new_tiers),len(new_foundations))

audit_modules={v for v in json.load(open(w/'preservation-module-plan.json'))['modules'].values() if v.startswith('scripts.audit.')}
backimports=[{'from':m,'to':dep} for m,deps in graph.items() if m.startswith('SerrePositivity.') for dep in deps&audit_modules]
(w/'audit-library-boundary.json').write_text(json.dumps({'audit_modules':sorted(audit_modules),'library_backimports':backimports},indent=2))
assert not backimports,backimports
mm=json.load(open(w/'module-map.json'));base=json.load(open(old/'preview-build-plan.json'))['modules'];delta=json.load(open(w/'before-targets.json'))
if isinstance(delta,dict):print('unexpected before-target keys',list(delta));raise SystemExit(1)
# IntegralExistence is the sole B2 destination explicitly retained at its original path.
a='SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence';proposed=json.load(open(old/'preservation-module-plan.json'))['modules'].get(a,a)
requested={a if m==proposed else m for m in base}|{mm.get(m,m) for m in delta}
missing_targets=sorted(m for m in requested if m not in graph);assert not missing_targets,missing_targets[:20]
closure=set(requested);todo=list(requested)
while todo:
 m=todo.pop()
 for dep in graph[m]:
  if dep in graph and dep.startswith('SerrePositivity.') and dep not in closure:closure.add(dep);todo.append(dep)
order=list(TopologicalSorter({m:graph[m]&closure for m in closure}).static_order());groups=[order[i:i+100] for i in range(0,len(order),100)]
plan={'requested':len(requested),'prerequisites':len(closure-requested),'modules':order,'groups':groups,'graph_sources':len(graph),'policy':'B2 approved full target set plus every frozen-main delta library module; Integral retained at original path; dependency closure explicit'}
(w/'target-build-plan.json').write_text(json.dumps(plan,indent=2));print('targets',len(requested),'closure',len(order),'groups',len(groups))
# Full original B2 comparison coverage plus all frozen-main delta library modules.
previous=[m for group in json.load(open(old/'preservation-groups.json')) for m in group]
originals=sorted(set(previous)|set(delta));(w/'preservation-original-modules.json').write_text(json.dumps(originals,indent=2));print('preservation modules',len(originals))
