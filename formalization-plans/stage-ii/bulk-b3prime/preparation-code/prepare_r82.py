from pathlib import Path
import json,sys
R=Path('/tmp/bulk-b3prime-preview');W=Path('/tmp/bulk-b3prime');T=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(T/'scripts/refactor'))
from split_module import prepare,module_doc
from lean_source import parse_source,render,add_import
from prune_imports import replace_imports
m='SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface';src=R/(m.replace('.','/')+'.lean')
d=json.loads((W/'r82-before.json').read_text());ss=[s for s in d['sources'] if s['module']==m];original=ss[0]['source']
# Restore only our prior partial preview; public worktree remains unchanged.
if src.read_text()!=original:
 previous=json.loads((W/'r82-multi-split-plan.json').read_text());assert src.read_text()==previous['changes'][m]['after'];src.write_text(original)
d={**d,'modules':[m],'sources':ss,'declarations':[r for r in d['declarations'] if r['module']==m]}
(W/'r82-initial-planning-snapshot.json').write_text(json.dumps(d,ensure_ascii=False))
splits=json.loads((T/'formalization-plans/stage-ii/bulk-b3prime/split-plan.proposed.json').read_text())['rows'][:2];sets=[set(s['declarations']) for s in splits];destinations=[s['new_path'][:-5].replace('/','.') for s in splits]
# Existing engine checks ownership, source/ranges, command integrity, and all keep/moved dependencies for the union.
# Multi-way render then partitions that same parsed source; no fabricated fresh snapshot positions.
for s in splits:
 p=R/s['new_path']
 if p.exists():
  assert p.read_text()==json.loads((W/'r82-multi-split-plan.json').read_text())['changes'][p.relative_to(R).as_posix()[:-5].replace('/','.')]['after'];p.unlink()
plan=prepare(R,m,destinations[1],set.union(*sets),d)
source=parse_source(original,str(src),snapshot=d,module=m)
row_names=set(source.declarations)
partition=[row_names-set.union(*sets),*sets]
texts=[render(source,names,side='keep' if i==0 else 'moved') for i,names in enumerate(partition)]
texts[0]=add_import(add_import(texts[0],destinations[0]),destinations[1])
imports0=['SerrePositivity.CommutativeAlgebra.Perfectoid.Defs','SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic','Mathlib.Algebra.Category.Ring.Basic','Mathlib.CategoryTheory.Comma.Over.Basic','Mathlib.CategoryTheory.ObjectProperty.FullSubcategory','Mathlib.Combinatorics.Quiver.ReflQuiver','Mathlib.RingTheory.Ideal.Quotient.Operations','Mathlib.RingTheory.KrullDimension.Basic','Mathlib.RingTheory.Valuation.ValuationRing']
imports1=['SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCategories','SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCompletion','SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid','SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons']
for i in [1,2]:
 texts[i]=replace_imports(texts[i],[imports0,imports1][i-1]);texts[i]=texts[i].replace('open SerrePositivity.InfinityCategories\n','').replace('open scoped Simplicial\n','')
 title=['通常の可換代数圏と perfectoid 標的の充満部分圏','導来完備化 H⁰ の通常の環の関手と標的圏の同値'][i-1]
 texts[i]=module_doc(texts[i],title+'\n\n概要：通常の環・圏の構成をまとめる。\n方針：元の宣言の型と本体を保つ。\n規約：nerve と指定錐は BS の界面で定める。\n使われ方：BS の導来 perfectoid 化界面。')
# Remove only empty retained sections and their local commands from each generated output.
for section,qual in [('Derived','noncomputable '),('Completion','noncomputable '),('Interface','')]:
 marker='@[expose] public '+qual+'section '+section
 if marker not in texts[1]:continue
 start=texts[1].index(marker);end=texts[1].index('end '+section,start)+len('end '+section)
 texts[1]=texts[1][:start]+texts[1][end:]
texts[1]=texts[1].replace('open CategoryTheory CategoryTheory.Limits MonoidalCategory','open CategoryTheory CategoryTheory.Limits')
start=texts[2].index('/-! ## 通常の代数への導来完備化')
header=texts[2][:texts[2].index('/-! ## Perfectoid 化界面')]
texts[2]=header+texts[2][start:texts[2].index('end Completion')+len('end Completion')]+'\n'
for i,names in enumerate(partition):
 for name in names:assert source.commands[source.declarations[name]].text in texts[i],name
for mod,text in zip([m,*destinations],texts):
 p=R/(mod.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
rows={r['name']:r for r in d['declarations']};wrong=[]
for name in sets[0]:
 for used in rows[name]['used_constants']:
  if used in sets[1]:wrong.append([name,used])
assert not wrong,wrong
plan['changes']={mod:{'before':original if i==0 else None,'after':text} for i,(mod,text) in enumerate(zip([m,*destinations],texts))};plan['partition']={mod:sorted(names) for mod,names in zip([m,*destinations],partition)};plan['planning_only']='Fresh baseline v3b; after snapshot and comparison still required'
(W/'r82-multi-split-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2));print('three-way source partition',list(map(len,partition)),'no categories-to-interface dependency',flush=True)
