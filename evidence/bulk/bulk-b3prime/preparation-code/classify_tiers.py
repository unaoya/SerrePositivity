from pathlib import Path
import json,sys,time,copy,collections
from graphlib import TopologicalSorter,CycleError
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');sys.path.insert(0,str(R/'scripts/refactor'));from klw1_layer_check import source_graph,check;from layer_check import under
full=json.loads((R/'scripts/refactor/layers.json').read_text());cfg=full['klw1'];original=copy.deepcopy(cfg);graph=source_graph(R,cfg['exclude_prefixes']);(W/'tracked-import-graph.json').write_text(json.dumps({m:sorted(ds) for m,ds in graph.items()}));missing=sorted(m for m in graph if under(m,'SerrePositivity.InfinityCategories') and m not in cfg['modules']);assert len(missing)==305,len(missing)
try:order=list(TopologicalSorter({m:ds&graph.keys() for m,ds in graph.items()}).static_order())
except CycleError as error:
 (W/'tier-classification-problems.json').write_text(json.dumps({'cycle':error.args[1]},indent=2));raise SystemExit(1)
new={}
for m in order:
 if m not in missing:continue
 deps={cfg['modules'].get(dep,'Consumers') for dep in graph[m] if dep in graph};tier='Consumers' if deps&{'Entrypoints','Consumers'} or any(any(under(dep,p) for p in cfg['implementation_prefixes']) for dep in graph[m]) else 'Comparison' if 'Comparison' in deps else 'Portable';cfg['modules'][m]=tier;new[m]={'tier':tier,'dependency_tiers':sorted(deps),'rule':'five per-file tiers in dependency order; independent IC files Portable, dependencies on Comparison stay Comparison, actual consumers of implementation or Entrypoints remain Consumers; no existing tier or exception changed'}
assert all(cfg['modules'][m]==v for m,v in original['modules'].items());assert all(cfg[k]==original[k] for k in cfg if k!='modules')
report=check(graph,cfg);(W/'new-main-tiers.json').write_text(json.dumps(new,ensure_ascii=False,indent=2)+'\n');(W/'tiers-candidate-layers.json').write_text(json.dumps(full,ensure_ascii=False,indent=2)+'\n');(W/'tiers-baseline-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n');summary={'baseline':'32d364b53','count':len(new),'counts':dict(collections.Counter(r['tier'] for r in new.values())),'existing_tiers_changed':0,'exceptions_changed':0,'violations':report['violations'],'rule_authorization':'coordinator/user reply 2026-11-14 night; use B3 rule; do not guess on violations'};(W/'tier-classification-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n');print(summary['counts'],'violations',len(summary['violations']));print(str(summary['violations'])[:1300])
