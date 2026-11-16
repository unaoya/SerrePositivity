"""Prepare source rewriting from native owned names; preserve source-only hints separately."""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,csv,json,sys
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--owners',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();base=root/'formalization-plans/stage-ii/organize-einfinity-w1';out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(root/'scripts/refactor'));from klw1_namespace import Migration,rename_prefix
files=list(csv.DictReader((base/'stage1-modules.csv').open()));by={r['old_module']:r for r in files};data=json.loads(a.owners.read_text());assert set(data['modules'])==set(by) and data['count']==len(data['declarations'])
modules={m:r['new_module'] for m,r in by.items()};namespaces={m:{r['old_namespace']:r['new_namespace']} for m,r in by.items() if r['action']=='move'};rows=[];owners=[];prefixes=defaultdict(set)
for d in data['declarations']:
 m=d['module'];user=d['name'];new=rename_prefix(user,namespaces.get(m,{}));old=d['kernel_name'] if d['is_private'] else user
 owners.append(dict(old_module=m,old=user,old_kernel_name=d['kernel_name'],new_module=modules[m],new=new,private=d['is_private'],new_kernel_name=None if d['is_private'] else new))
 if user!=new:rows.append(dict(module=m,old=old,new=new))
 if not d['is_private'] and user!=new:
  parent=user.rpartition('.')[0]
  while parent:
   newparent=rename_prefix(parent,namespaces.get(m,{}))
   if parent!=newparent:prefixes[parent].add(newparent)
   parent=parent.rpartition('.')[0]
opens={
 'SerrePositivity.EInfinity.HomotopyWeight':'SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight',
 'SerrePositivity.EInfinity.FrameHom':'SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom',
 'SerrePositivity.EInfinity.SimplicialLocalization':'SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization',
 'SerrePositivity.EInfinity.BarrattEccles':'SerrePositivity.EInfinity.BarrattEccles'}
ambiguous=[]
for old,targets in prefixes.items():
 if old in opens:continue
 if len(targets)==1:opens[old]=next(iter(targets))
 else:ambiguous.append(dict(old=old,new=sorted(targets)))
plan=dict(modules=modules,namespaces=namespaces,opens=opens,module_opens={},rows=rows)
Migration(plan)
(out/'namespace-rewrite-map.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n');(out/'public-owner-map.json').write_text(json.dumps(dict(policy='native before ownership; expected new canonical names; private after kernel names must be observed',rows=owners),ensure_ascii=False,indent=2)+'\n')
counts=Counter(d['module'] for d in data['declarations']);summary=dict(modules=len(modules),native_declarations=len(owners),private_declarations=sum(d['is_private'] for d in data['declarations']),renamed_public=sum(not r['private'] and r['old']!=r['new'] for r in owners),renamed_private_user_names=sum(r['private'] and r['old']!=r['new'] for r in owners),zero_declaration_modules=[m for m in by if not counts[m]],ambiguous_open_prefixes=ambiguous,validated_by_existing_Migration=True,stage='prepared; original-source reference capture and preview review still required; not yet applied')
(out/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n');print(json.dumps(summary,ensure_ascii=False))
