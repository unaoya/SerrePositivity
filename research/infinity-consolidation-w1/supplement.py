"""段0のB1/B4・境界・choose継承の補助集計（ソースのみ）。"""
from pathlib import Path
import json,csv,pickle,collections,hashlib,sys
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT));from importlib.util import spec_from_file_location,module_from_spec
sys.path.insert(0,str(ROOT/'scripts/refactor'));from layer_check import imports
_,g=pickle.loads(Path('/private/tmp/ic-w1-stage0-graph.pickle').read_bytes())
moves=list(csv.DictReader((OUT/'moves.csv').open()));move={r['old_module']:r['new_module'] for r in moves};rev=collections.defaultdict(set)
for m,ds in g.items():
 for d in ds:rev[d].add(m)
def closure(starts):
 seen=set(starts);todo=list(starts)
 while todo:
  for d in rev[todo.pop()]:
   if d not in seen:seen.add(d);todo.append(d)
 return seen
def dump(n,a):(OUT/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
def table(n,a):
 with (OUT/n).open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(a[0]),lineterminator='\n');w.writeheader();w.writerows(a)
bychapter=collections.defaultdict(list)
for m in g:
 if not m.startswith('SerrePositivity.InfinityCategories.'):continue
 p=m.replace('.','/')+'.lean';lines=len((ROOT/p).read_text().splitlines())
 if lines<=80:bychapter[str(Path(p).parent)].append((p,lines))
table('b1-chapter-candidates.csv',[dict(directory=d,small_files=len(a),lines=sum(n for _,n in a),paths=';'.join(p for p,_ in a)) for d,a in sorted(bychapter.items())])
# Boundary inventory: general candidates still tied to concrete EInfinity implementation.
be_prefix=('SerrePositivity.EInfinity.BarrattEccles','SerrePositivity.EInfinity.IntervalCuts','SerrePositivity.EInfinity.SimplexCuts','SerrePositivity.EInfinity.Surjection','SerrePositivity.EInfinity.TableReduction','SerrePositivity.EInfinity.BergerFresse')
bound=[]
for r in moves:
 if r['classification']=='BE固有':continue
 ds=sorted(d for d in g[r['old_module']] if d.startswith(be_prefix))
 if ds:bound.append(dict(path=r['old_path'],new_path=r['new_path'],imports=';'.join(ds),count=len(ds)))
table('concrete-boundary-imports.csv',bound)
imp=[(m,d) for m,ds in g.items() if m not in move for d in ds if d in move]
a=json.loads((OUT/'choose-inherited.json').read_text());changed=[];missing=[]
for r in a['definitions']:
 p=ROOT/r['file']
 if not p.exists():missing.append(r['id'])
 elif hashlib.sha256(p.read_bytes()).hexdigest()!=r['source_sha256']:changed.append(r['id'])
lanes=json.loads((OUT/'branch-impact.json').read_text());dependents=closure(move)
for b,l in lanes.items():
 wt=Path(l['worktree']);affected=[]
 for p in l.get('touched_paths',[]):
  if not (wt/p).exists():continue
  ds=imports((wt/p).read_text());hs=sorted(ds&dependents)
  if hs:affected.append(dict(path=p,indirect_imports=hs))
 l['transitive_rebuild_candidate_files']=len(affected);l['transitive_rebuild_import_edges']=sum(len(x['indirect_imports']) for x in affected)
 # No need to store thousands of repeated source import strings in the paper.
 l['transitive_rebuild_candidate_paths']=[r['path'] for r in affected]
# Branch snapshot is read-only here; final-branches.py owns the final observation.
summary=dict(small_files=sum(len(a) for a in bychapter.values()),small_chapters=len(bychapter),small_top20=[(k,len(v),sum(n for _,n in v)) for k,v in sorted(bychapter.items(),key=lambda x:-len(x[1]))[:20]],concrete_bound_files=len(bound),concrete_bound_edges=sum(r['count'] for r in bound),external_importer_files=len({m for m,_ in imp}),external_import_edges=len(imp),inherited_sha_different=changed,inherited_missing=missing,formal_audits=sum(bool(x.strip()) and not x.startswith('#') for x in (ROOT/'scripts/refactor/audit_manifest.txt').read_text().splitlines()),inherited_source_head=a.get('source_head'))
dump('supplement-summary.json',summary);print(json.dumps(summary,ensure_ascii=False,indent=2))
