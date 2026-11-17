from pathlib import Path
import json,sys,hashlib,re
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');D=R/'evidence/bulk/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'))
from lean_source import parse_source,add_import,doc_start
from split_module import prepare,module_doc
from prune_imports import replace_imports
from doc_plan import comments
def noncomments(source):
 parts=[];at=0
 for lo,hi in comments(source):parts.append(source[at:lo]);at=hi
 parts.append(source[at:]);return "".join(parts)
status=json.loads((W/'rewrite-status.json').read_text());migration=json.loads((W/'namespace-rewrite-plan.json').read_text());splits=json.loads((D/'split-plan.proposed.json').read_text())['rows'];name_rows=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];snapshots={}
for file in (W/'before').glob('group-*.json'):
 if not file.with_name(file.stem+'.complete.json').exists():continue
 d=json.loads(file.read_text())
 for m in d['modules']:snapshots[m]={**d,'modules':[m],'sources':[s for s in d['sources'] if s['module']==m],'declarations':[r for r in d['declarations'] if r['module']==m]}
outputs={};records=[]
def module(path):return path[:-5].replace('/','.')
def project(text,edits,a,b):
 raw=text.encode();lo=len(text[:a].encode());hi=len(text[:b].encode());at=lo;result=bytearray()
 for e in edits:
  x,y=e['start'],e['stop'];selected=lo<x<=hi or lo==x==0 if x==y else lo<=x and y<=hi
  if not selected:
   if x<hi and lo<y:raise ValueError('edit crosses command boundary '+str(e))
   continue
  assert x>=at;result.extend(raw[at:x]);result.extend(e['replacement'].encode());at=y
 result.extend(raw[at:hi]);return result.decode()
def scoped_render(source,selected,edits):
 wanted={i for i,c in enumerate(source.commands) if c.kind=='header'};contexts=set()
 for name in selected:
  i=source.declarations[name];wanted.add(i);contexts.update(source.commands[i].context)
 wanted.update(contexts);scopes={i for i in contexts if source.commands[i].kind=='scope'}
 for i,c in enumerate(source.commands):
  if c.kind!='attribute':continue
  local=bool(re.search(r'\b(?:local|scoped)\b',c.attribute_spec));parents={p for _,p in c.attribute_targets if p};here=parents&selected
  if here and parents-selected:raise ValueError('attribute crosses partition '+c.text)
  external=any(p is None for _,p in c.attribute_targets)
  attr_scopes={j for j in c.context if source.commands[j].kind=='scope'}
  if here or external and local and attr_scopes<=scopes:wanted.add(i);wanted.update(c.context)
 for i,c in enumerate(source.commands):
  if c.kind=='end' and c.closes in wanted:wanted.add(i)
 return ''.join(project(source.text,edits,c.start,c.end) for i,c in enumerate(source.commands) if i in wanted)
def section(text,label):
 s=text.index('@[expose] public noncomputable section '+label);a=text.rfind('/-!',0,s);b=text.index('end '+label,s)+len('end '+label);assert a>=0
 if text[b:b+1]=='\n':b+=1
 return a,b
def header(imports,title,universes):
 return 'module\n'+''.join('public import '+m+'\n' for m in sorted(set(imports)))+'\n/-!\n# '+title+'\n\n概要：一般の構成とその比較をまとめる。\n方針：元の型・本体・局所的な文脈を、機械的な名前の追従だけで保存する。\n規約：特殊な包絡の存在や追加の仮定を導入しない。\n使われ方：Bhatt–Scholze の包絡または perfectoid 化の比較。\n-/\n\nuniverse '+universes+'\n\n'
for oldpath in sorted({s['old_path'] for s in splits}):
 oldmod=module(oldpath)
 if oldpath not in status['files'] or oldmod not in snapshots:continue
 text=(R/oldpath).read_text();snap=snapshots[oldmod];assert len(snap['sources'])==1 and snap['sources'][0]['source']==text;edits=json.loads((W/'rewritten'/(oldmod+'.edits.json')).read_text());targets=[s for s in splits if s['old_path']==oldpath];newmods=[module(s['new_path']) for s in targets];selections=[set(s.get('declarations',[])) or {r['old'] for r in name_rows if r['old_module']==oldmod and r['new_module']==n} for s,n in zip(targets,newmods)];allselected=set.union(*selections);retainedmod=migration['modules'].get(oldmod,oldmod);extra={};evidence={}
 if oldpath.endswith('/Derived/Interface.lean') or oldpath.endswith('/Derived/IntegralExistence.lean'):
  # Original engine checks source positions, dependencies, and attribute boundaries for the union.
  trial=prepare(R,oldmod,'SerrePositivity.BhattScholze.Perfectoidization.Interface.SplitPlanningUnion',allselected,snap);evidence['dependencies']=trial['dependencies'];source=parse_source(text,oldpath,snapshot=snap,module=oldmod);keep=set(source.declarations)-allselected;retained=scoped_render(source,keep,edits)
  for s,n,selected in zip(targets,newmods,selections):
   rendered=scoped_render(source,selected,edits)
   if n.endswith('.RingCategories'):
    deps=['Mathlib.Algebra.Category.Ring.Basic','Mathlib.CategoryTheory.Comma.Over.Basic','Mathlib.CategoryTheory.ObjectProperty.FullSubcategory','Mathlib.Combinatorics.Quiver.ReflQuiver','Mathlib.RingTheory.Ideal.Quotient.Operations','Mathlib.RingTheory.KrullDimension.Basic','Mathlib.RingTheory.Valuation.ValuationRing','SerrePositivity.CommutativeAlgebra.Perfectoid.Defs','SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic'];rendered=replace_imports(rendered,deps);rendered=rendered.replace('open SerrePositivity.InfinityCategories\n','').replace('open _root_.SerrePositivity.InfinityCategories\n','').replace('open scoped Simplicial\n','').replace('open scoped _root_.Simplicial\n','').replace('open CategoryTheory CategoryTheory.Limits MonoidalCategory','open CategoryTheory CategoryTheory.Limits').replace('open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory','open _root_.CategoryTheory _root_.CategoryTheory.Limits');rendered=module_doc(rendered,'# 通常の可換代数圏と perfectoid 標的の充満部分圏\n\nnerve・指定錐と独立な通常の圏、商図式、付値環への一意延長条件。')
   elif n.endswith('.RingInterface'):
    deps=['SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCategories','SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingCompletion','SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid','SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons'];rendered=replace_imports(rendered,deps).replace('open SerrePositivity.InfinityCategories\n','').replace('open _root_.SerrePositivity.InfinityCategories\n','').replace('open scoped Simplicial\n','').replace('open scoped _root_.Simplicial\n','');rendered=module_doc(rendered,'# 導来完備化 H⁰ の通常の環の関手\n\n完備な標的への延長と、その標的圏の同値。')
   elif s.get('source_section')=='InitialLimit':
    deps={dep for row in snap['declarations'] if any(row['name']==x or row['name'].startswith(x+'.') for x in selected) for dep in row['used_modules'] if dep.startswith(('Mathlib.','SerrePositivity.')) and dep!=oldmod};assert not any('BhattScholze' in dep for dep in deps);rendered=replace_imports(rendered,deps);rendered=module_doc(rendered,'# 始対象の値から指定極限錐を計算する\n\n一般の∞圏の共終性を使い、指定された始対象から極限錐を計算する。')
   elif s.get('source_section')=='InitialBridge':rendered=add_import(rendered,newmods[0]);rendered=module_doc(rendered,'# 指定された普遍 perfectoid 化と導来極限の比較\n\n普遍単位を標的圏の始対象として使い、指定錐の比較から離散性を得る。')
   extra[n]=rendered
 elif oldpath.endswith('/RootSource.lean') or oldpath.endswith('/DivisionResidue.lean'):
  labels=['IteratedPDH0Reflection'] if oldpath.endswith('/RootSource.lean') else ['DeltaAdjoinDivisionResiduePresentation','DeltaDivisionSourceResidueTensor'];spans=[section(text,label) for label in labels];ranges=sorted(spans);parts=[];at=0
  for a,b in ranges:parts.append(project(text,edits,at,a));at=b
  parts.append(project(text,edits,at,len(text)));retained=''.join(parts);selected=selections[0];rows=[r for r in snap['declarations'] if any(r['name']==x or r['name'].startswith(x+'.') for x in selected)];deps={dep for row in rows for dep in row['used_modules'] if dep.startswith(('Mathlib.','SerrePositivity.')) and dep!=oldmod}
  if labels[0]=='IteratedPDH0Reflection':assert not any('BhattScholze' in dep for dep in deps)
  else:assert not any('.Andre.' in dep for dep in deps)
  extra[newmods[0]]=header(deps,'二つの主元完備化の H⁰ と PD 完備化の比較' if labels[0]=='IteratedPDH0Reflection' else 'δ 除算添加環の剰余とテンソル表示','u' if labels[0]=='IteratedPDH0Reflection' else 'u v')+'\n'.join(project(text,edits,a,b) for a,b in spans);evidence['source_spans']=spans;evidence['note']='Source-local notations exceed conservative splitter syntax; preserve complete self-contained sections and their exact indexed edits. Full v3b including native parser descriptors remains mandatory.'
 elif oldpath.endswith('/Transfinite/Limit.lean'):
  a=doc_start(text,text.index('theorem mul_eq_zero_of_pow_mul_eq_zero_of_reduced'));b=text.index('/--',text.index('theorem mul_eq_zero_of_pow_mul_eq_zero_of_reduced'));retained=project(text,edits,0,a)+project(text,edits,b,len(text));r=next(r for r in snap['declarations'] if r['name'] in selections[0]);deps=[dep for dep in r['used_modules'] if dep.startswith('Mathlib.')]+['Mathlib.Tactic.Ring'];extra[newmods[0]]=header(deps,'被約可換環の冪による消滅','u')+'@[expose] public noncomputable section\n\n'+project(text,edits,a,b)+'\nend\n';evidence['source_spans']=[[a,b]]
 else:raise ValueError(oldpath)
 partition_before_docs={retainedmod:retained,**extra}
 # Context commands can carry the preceding module-level section comment.
 # Keep only the section description belonging to this partition; no Lean token changes.
 if oldpath.endswith('/Derived/IntegralExistence.lean'):
  retained=module_doc(retained,'# 整代数と有限代数の普遍 perfectoid 化の存在\n\n導来 perfectoid 化の界面から整代数の普遍環を取り出し、公開入口と完備化への比較を与える。始対象の一般計算と指定単位の比較は別の二つのモジュールに分離する。')
  for n in [retainedmod,*newmods]:
   source=retained if n==retainedmod else extra[n]
   if not n.endswith('.InitialValueCone'):
    source=re.sub(r'/\-! ## 始対象の値による指定極限錐の計算.*?\-/','',source,flags=re.S)
   if n==retainedmod:retained=source
   else:extra[n]=source
 if oldpath.endswith('/Derived/Interface.lean'):
  retained=module_doc(retained,'# 導来 perfectoid 化の指定界面\n\n通常の環の添字圏と完備化関手は環側の二つのモジュールから受け取り、導来対象・指定極限錐・単位・離散時の普遍性をまとめる。')
  for n in [retainedmod,*newmods]:
   source=retained if n==retainedmod else extra[n]
   if not n.endswith('.RingCategories'):
    source=re.sub(r'/\-! ## Perfectoid 化界面の通常の添字圏.*?\-/','',source,flags=re.S)
   if n==retainedmod:retained=source
   else:extra[n]=source
 for n,source in {retainedmod:retained,**extra}.items():assert noncomments(source)==noncomments(partition_before_docs[n]),('partition doc update changed Lean tokens',n)
 for n in newmods:retained=add_import(retained,n)
 outputs[retainedmod]=retained;outputs.update(extra);records.append({'old_module':oldmod,'retained_module':retainedmod,'new_modules':newmods,'declarations':{n:sorted(v) for n,v in zip(newmods,selections)},**evidence})
out=W/'split-bundle';out.mkdir(exist_ok=True)
for mod,text in outputs.items():
 p=out/(mod.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
(out/'plan.json').write_text(json.dumps({'status':'projected sources only; not applied; complete after-build v3b and full bundle gates required','records':records,'files':{m:hashlib.sha256(s.encode()).hexdigest() for m,s in outputs.items()}},ensure_ascii=False,indent=2));print('projected split sources',len(outputs),'original modules',len(records))
