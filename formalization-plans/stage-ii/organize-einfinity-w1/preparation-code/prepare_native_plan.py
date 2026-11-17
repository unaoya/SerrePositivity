"""Prepare source rewriting from native owned names; preserve source-only hints separately."""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,csv,json,sys,re
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--owners',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--original-root',type=Path,required=True);a=p.parse_args();root=a.root.resolve();base=root/'formalization-plans/stage-ii/organize-einfinity-w1';out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
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
# Demand-generated equation/congruence declarations can have a foreign parent.
# Confirm absence of a source declaration; follow its actual parent, never an ordinal.
public={r['old']:r for r in owners if not r['private']};ilean={};compiler_children=[];corrections=[]
for r in sorted(owners,key=lambda r:len(r['old'].split('.'))):
 if r['private'] or not re.search(r'\.(?:congr_simp|eq_\d+)$',r['old']):continue
 m=r['old_module']
 if m not in ilean:ilean[m]=json.loads((a.original_root/'.lake/build/lib/lean'/(m.replace('.','/')+'.ilean')).read_text())['decls']
 if r['old_kernel_name'] in ilean[m]:continue
 parent=r['old'].rpartition('.')[0];found=None
 while parent:
  if parent in public:found=public[parent];break
  parent=parent.rpartition('.')[0]
 target=found['new']+r['old'][len(parent):] if found else r['old']
 record=dict(module=m,old=r['old'],default=r['new'],parent=parent if found else r['old'].rpartition('.')[0],parent_selected=bool(found),expected=target,source_decl_present=False)
 compiler_children.append(record)
 if target!=r['new']:corrections.append(record);r['new']=target
 r['classification']='source-free compiler equation/congruence; after provider must be observed'
foreign_private=[dict(module=r['old_module'],kernel_name=r['old_kernel_name'],name=r['old'],expected=r['new'],classification='foreign private compiler declaration; after provider must be observed') for r in owners if r['private'] and not r['old_kernel_name'].startswith('_private.'+r['old_module']+'.')]
rows=[dict(module=r['old_module'],old=r['old_kernel_name'] if r['private'] else r['old'],new=r['new']) for r in owners if r['old']!=r['new']]
(out/'compiler-child-parent-review.json').write_text(json.dumps(dict(inventory=compiler_children,corrections=corrections,foreign_private=foreign_private),ensure_ascii=False,indent=2)+'\n')
# Rebuild deep opens from the corrected canonical parent identities.
prefixes=defaultdict(set)
for r in owners:
 if r['private'] or r['old']==r['new']:continue
 parent=r['old'].rpartition('.')[0]
 while parent:
  newparent=public[parent]['new'] if parent in public else rename_prefix(parent,namespaces.get(r['old_module'],{}))
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
counts=Counter(d['module'] for d in data['declarations']);summary=dict(modules=len(modules),native_declarations=len(owners),private_declarations=sum(d['is_private'] for d in data['declarations']),renamed_public=sum(not r['private'] and r['old']!=r['new'] for r in owners),renamed_private_user_names=sum(r['private'] and r['old']!=r['new'] for r in owners),zero_declaration_modules=[m for m in by if not counts[m]],compiler_equation_congruence_declarations=len(compiler_children),compiler_child_target_corrections=len(corrections),foreign_private_compiler_declarations=len(foreign_private),ambiguous_open_prefixes=ambiguous,validated_by_existing_Migration=True,stage='prepared; original-source reference capture and preview review still required; not yet applied')
(out/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n');print(json.dumps(summary,ensure_ascii=False))
