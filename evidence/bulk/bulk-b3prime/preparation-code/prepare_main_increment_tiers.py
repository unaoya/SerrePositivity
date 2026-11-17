from pathlib import Path
from graphlib import TopologicalSorter,CycleError
import json,sys,subprocess,collections,copy
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');M=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity');sys.path.insert(0,str(R/'scripts/refactor'));from klw1_layer_check import check;from layer_check import under,imports
impact=json.loads((W/'main-increment-impact.json').read_text());head=impact['main'];g={m:set(ds) for m,ds in json.loads((W/'tracked-import-graph.json').read_text()).items()};full=json.loads((W/'tiers-candidate-layers.json').read_text());cfg=full['klw1'];original=copy.deepcopy(cfg);files=subprocess.check_output(['git','diff','--name-only','32d364b53',head,'--','SerrePositivity','SerrePositivity.lean'],cwd=M,text=True).splitlines()
for rel in files:
 if not rel.endswith('.lean') or rel.startswith('SerrePositivity/Archive/'):continue
 p=M/rel;m=rel[:-5].replace('/','.')
 if p.exists():g[m]=set(imports(p.read_text()))
 else:g.pop(m,None)
missing=set(m for m in g if under(m,'SerrePositivity.InfinityCategories') and m not in cfg['modules']);new={};problems=[]
try:order=list(TopologicalSorter({m:ds&g.keys() for m,ds in g.items()}).static_order())
except CycleError as e:problems.append({'cycle':e.args[1]});order=[]
for m in order:
 if m not in missing:continue
 deps={cfg['modules'].get(d,'Consumers') for d in g[m] if d in g};tier='Consumers' if deps&{'Entrypoints','Consumers'} or any(any(under(d,p) for p in cfg['implementation_prefixes']) for d in g[m]) else 'Comparison' if 'Comparison' in deps else 'Portable';cfg['modules'][m]=tier;new[m]={'tier':tier,'dependency_tiers':sorted(deps),'rule':'five per-file tiers in dependency order; independent IC files Portable, dependencies on Comparison stay Comparison, actual consumers of implementation or Entrypoints remain Consumers; no existing tier or exception changed'}
assert all(cfg['modules'][m]==v for m,v in original['modules'].items());assert all(cfg[k]==original[k] for k in cfg if k!='modules');report=check(g,cfg);blocking=[r for r in report['violations'] if r['kind']!='reverse-section'];summary={'main':head,'baseline':'32d364b53','additional_IC_modules':len(new),'counts':dict(collections.Counter(r['tier'] for r in new.values())),'undecided':problems,'violations':report['violations'],'non_section_order_violations':blocking,'existing_tiers_changed':0,'exceptions_changed':0,'status':'Read-only proposal for main increments; reconcile again at application, no source or actual configuration applied.'};(W/'main-increment-tiers.json').write_text(json.dumps(new,ensure_ascii=False,indent=2));(W/'main-increment-tiers-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('additional',len(new),summary['counts'],'undecided',len(problems),'violations',len(report['violations']),'blocking',len(blocking));raise SystemExit(bool(problems or blocking))
