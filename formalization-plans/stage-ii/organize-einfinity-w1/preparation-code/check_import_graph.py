"""Compare all active project import edges with exact whole-file transport."""
from pathlib import Path
from graphlib import TopologicalSorter
from collections import defaultdict,deque
import argparse,gzip,hashlib,json,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--before',type=Path);a=p.parse_args();root=a.root.resolve();base=root/'formalization-plans/stage-ii/organize-einfinity-w1';sys.path.insert(0,str(root/'scripts/refactor'));from layer_check import imports
paths=subprocess.check_output(['git','ls-files','-z','--','SerrePositivity','SerrePositivity.lean'],cwd=root).decode().split('\0');g={}
for path in paths:
 if not path.endswith('.lean') or path.startswith('SerrePositivity/Archive/'):continue
 g[path[:-5].replace('/','.')]=imports((root/path).read_text())
project=lambda m:m=='SerrePositivity' or m.startswith('SerrePositivity.')
missing=[dict(module=m,dependency=d) for m,ds in g.items() for d in ds if project(d) and d not in g];assert not missing,missing[:20]
order=list(TopologicalSorter({m:ds&g.keys() for m,ds in g.items()}).static_order());assert len(order)==len(g)
mm=json.loads((base/'module-map.json').read_text());rename=lambda m:mm.get(m,m)
def closure(seeds,graph):
 seen=set(seeds);q=deque(seeds)
 while q:
  for d in graph.get(q.popleft(),set()):
   if d not in seen:seen.add(d);q.append(d)
 return seen
summary=dict(modules=len(g),edges=sum(map(len,g.values())),missing_project_imports=missing,cycle=False,transport_checked=False)
a.output.mkdir(parents=True,exist_ok=True)
if a.before:
 with gzip.open(a.before,'rt') as f:old={m:set(ds) for m,ds in json.load(f).items()}
 expected={rename(m):{rename(d) for d in ds} for m,ds in old.items()};assert set(expected)==set(g)
 allowed={r['new_path'][:-5].replace('/','.') for r in json.loads((base/'preparation/citation-review-all-native.json').read_text())['records'] if not r['existing_source_attribute']};changes=[]
 for m in g:
  added=g[m]-expected[m];removed=expected[m]-g[m]
  if added or removed:
   assert not removed and m in allowed and added=={'Mathlib.Tactic.CrossRefAttribute'},(m,added,removed)
   changes.append(dict(module=m,added=sorted(added),removed=sorted(removed)))
 summary.update(transport_checked=True,explicit_metadata_imports=changes)
 # Topological target order also includes invalidated dependencies between selected callers.
 targets={rename(m) for m in json.loads(Path('/private/tmp/oe-w1-reference-candidates/preservation-modules.json').read_text())};assert targets<=g.keys();needed=closure(targets,g)&g.keys();rev=defaultdict(set)
 for m,ds in g.items():
  for d in ds:rev[d].add(m)
 application=json.loads(Path('/private/tmp/oe-w1-application/application.json').read_text());dirty={p[:-5].replace('/','.') for p in application['paths_to_write'] if p.endswith('.lean') and p[:-5].replace('/','.') in g};affected=closure(dirty,rev)&needed;build_order=[m for m in order if m in targets|affected]
 (a.output/'target-build-order.json').write_text(json.dumps(build_order,indent=2)+'\n');summary.update(selected_targets=len(targets),invalidated_needed_modules=len(affected),ordered_build_modules=len(build_order))
 old_root=closure({'SerrePositivity'},old)&old.keys();root_reachable=closure({'SerrePositivity'},g)&g.keys();assert root_reachable=={rename(m) for m in old_root}
 summary.update(root_reachability_preserved=True,root_reachable_project_modules=len(root_reachable),baseline_stage1_not_root_reachable=sorted(set(mm)-old_root),after_stage1_not_root_reachable=sorted({rename(m) for m in mm}-root_reachable))
with gzip.open(a.output/'graph.json.gz','wt') as f:json.dump({m:sorted(ds) for m,ds in g.items()},f,sort_keys=True)
(a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
