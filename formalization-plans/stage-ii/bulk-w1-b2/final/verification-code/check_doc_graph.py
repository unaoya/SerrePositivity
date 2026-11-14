"""Static checks over actual rendered sources, including newly archived files."""
from pathlib import Path
import sys,json,graphlib,collections,hashlib
W=Path('/tmp/bulk-w1-b2');V=W/'replay-tree';R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import imports;from klw1_layer_check import check
plan=json.loads((W/'preview-build-plan.json').read_text());extra=[p[:-5].replace('/','.') for p in json.loads((W/'native-tag-extra-files.json').read_text())];roots=set(plan['modules'])|set(extra);all_sources={str(p.relative_to(V))[:-5].replace('/','.'):p for p in (V/'SerrePositivity').rglob('*.lean')};all_sources['SerrePositivity']=V/'SerrePositivity.lean'
comparison_plan=json.load(open(W/'preservation-module-plan.json'));comparison_old=[s[:-5].replace('/','.') for s in json.load(open(W/'comparison-files.json'))]
roots|={comparison_plan['modules'].get(m,m) for m in comparison_old}|{d for m in comparison_old for d in comparison_plan.get('declarations',{}).get(m,{}).values()}
audit_paths=json.load(open(W/'evening-audit-plan.json'))['standalone_audits'];audit_modules={p[:-5].replace('/','.') for p in audit_paths}
all_sources.update({p[:-5].replace('/','.'):V/p for p in audit_paths})
graph={};pending=list(roots);missing=[]
while pending:
 module=pending.pop()
 if module in graph:continue
 path=all_sources.get(module)
 if not path:missing.append(module);continue
 dependencies=imports(path.read_text());graph[module]=dependencies
 pending.extend(d for d in dependencies if (d.startswith('SerrePositivity') or d in audit_modules) and d not in graph)
cycles=[]
try:order=list(graphlib.TopologicalSorter({m:ds&graph.keys() for m,ds in graph.items()}).static_order())
except graphlib.CycleError as e:cycles.append(e.args[1]);order=[]
active={m:ds for m,ds in graph.items() if m.startswith('SerrePositivity') and not m.startswith('SerrePositivity.Archive.')};cfg=json.loads((W/'layers-proposed.json').read_text());cfg['modules']={m:t for m,t in cfg['modules'].items() if m in active};
for key in ['implementation_edges','reverse_edges']:cfg[key]=[e for e in cfg[key] if e['from'] in active and e['to'] in active[e['from']]]
report=check(active,cfg);report.pop('topological_order',None);audit_backimports=[{'from':m,'to':d} for m,ds in graph.items() if m.startswith('SerrePositivity') for d in ds if d in audit_modules];result={'standalone_audit_roots':len(audit_modules),'library_imports_of_moved_audits':audit_backimports,'import_parser':'layer_check.imports (all modules on a directive, comments and strings masked)','root_targets':len(roots),'local_closure':len(graph),'static_edges':sum(map(len,graph.values())),'missing_project_imports':sorted(set(missing)),'cycles':cycles,'layer_violations':report['violations'],'new_exception_status':'pending coordinator review; see new-reverse-edge-proposal.json','source_sha256':hashlib.sha256(json.dumps({m:hashlib.sha256(all_sources[m].read_bytes()).hexdigest() for m in sorted(graph)},sort_keys=True).encode()).hexdigest()};(W/'final-comment-graph-summary.json').write_text(json.dumps(result,indent=2));print({k:v for k,v in result.items() if k!='source_sha256'});raise SystemExit(bool(missing or cycles or report['violations'] or audit_backimports))
