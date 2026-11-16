from pathlib import Path
from collections import Counter
import subprocess,json,csv,re,hashlib
root=Path.cwd();out=root/'formalization-plans/stage-ii/organize-einfinity-w1'
def git(*args):return subprocess.check_output(['git',*args],text=True).strip()
base=git('rev-parse','HEAD');manifest=json.loads((root/'formalization-plans/stage-ii/is-w2-be-20261114-modules.json').read_text());scope=set(manifest)
groups={
'HomotopyWeight':('OE02','SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight','SerrePositivity.EInfinity.HomotopyWeight','射影cofibrant重み・BK・Kan係数と重み付き切断の一般論'),
'FrameHom':('OE03','SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom','SerrePositivity.EInfinity.FrameHom','一般の模型圏のframe Homと局所化の比較'),
'SimplicialLocalization':('OE04','SerrePositivity.InfinityCategories.HTT.ModelCategoryLocalization.SimplicialLocalization','SerrePositivity.EInfinity.SimplicialLocalization','HTT 1.3.4 の模型圏とその∞局所化・相対圏の補助')}
for d in groups:scope.update(str(p.relative_to(root).with_suffix('')).replace('/','.') for p in (root/'SerrePositivity/EInfinity'/d).rglob('*.lean'))
rows=[]
for m in sorted(scope):
 p=root/(m.replace('.','/')+'.lean');s=p.read_text();ns=sorted(set(re.findall(r'^namespace\s+(\S+)',s,re.M)))
 if m.startswith('SerrePositivity.EInfinity.BarrattEccles.'):
  id='OE05';new=m.replace('SerrePositivity.EInfinity.BarrattEccles.','SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.',1);oldns='SerrePositivity.EInfinity.BarrattEccles';newns=oldns+'.StoppedRoutes.ISW2Tot';reason='D81で停止したBE値のIS-W2 Tot比較。所有宣言単位で改名し、BE全体のnamespaceは一括置換しない'
 else:
  d=next((d for d in groups if m.startswith('SerrePositivity.EInfinity.'+d+'.')),None)
  if d:
   id,newprefix,oldns,reason=groups[d];new=m.replace(oldns,newprefix,1);newns=newprefix
  else:id='OE01';new=m;oldns='（現状維持）';newns=oldns;reason='274本中、既にKerodon/HomotopicalAlgebra等へ置かれた一般部品。再移動しない'
 if m in ['SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection','SerrePositivity.EInfinity.FrameHom.AnodyneFamilyHomotopy']:
  kp='SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes'
  new=kp+'.'+p.stem
  oldns='SerrePositivity.EInfinity.FrameHom'+('.AnodyneWeakDetection' if p.stem=='AnodyneWeakDetection' else '')
  newns=kp+('.AnodyneWeakDetection' if p.stem=='AnodyneWeakDetection' else '')
  reason='Kan標的によるanodyne局所化の検出・全族ホモトピー。Kerodon 3.1/3.3の同じ配置へ'
 dest=new.replace('.','/')+'.lean'
 assert new==m or not (root/dest).exists(),dest
 rows.append(dict(id=id,old_module=m,new_module=new,old_path=str(p.relative_to(root)),new_path=dest,old_namespace=oldns,new_namespace=newns,source_namespace_commands=';'.join(ns),lines=len(s.splitlines()),source_sha256=hashlib.sha256(s.encode()).hexdigest(),action='keep' if new==m else 'move',basis=reason))
assert len(rows)==588 and len({r['new_path'] for r in rows})==588
with (out/'stage1-modules.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(out/'stage1-files.json').write_text(json.dumps([r['old_path'] for r in rows],indent=2)+'\n')
(out/'module-map.json').write_text(json.dumps({r['old_module']:r['new_module'] for r in rows},indent=2)+'\n')
# Scope-narrowed namespace targets, not yet a compiler-derived declaration rewrite map.
(out/'namespace-targets.json').write_text(json.dumps({'status':'stage0 proposal; compiler ownership and private names must be captured before applying','groups':[dict(id=id,old=old,new=new,policy='owned declarations only') for id,new,old,_ in groups.values()]+[dict(id='OE05',old='SerrePositivity.EInfinity.BarrattEccles',new='SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot',policy='only declarations owned by the 99 listed files; preserve operad/CAlg_R and all other BE declarations')]},ensure_ascii=False,indent=2)+'\n')
# Whole remaining EInfinity inventory at frozen baseline; stage1-touched files marked.
excluded={'BarrattEccles','Interface','PowerOperation','Modules'}
s1old={r['old_path'] for r in rows if r['action']=='move'}
classrows=[]
be={'BergerFresse','IntervalCuts','SimplexCuts','Surjection','TableReduction'}
for p in sorted((root/'SerrePositivity/EInfinity').rglob('*.lean')):
 rel=p.relative_to(root);part=p.relative_to(root/'SerrePositivity/EInfinity').parts[0]
 if part.removesuffix(".lean") in excluded:continue
 if part in be:cl='BE固有';basis='Berger–Fresseの具体的な作用・全射語・table reductionとその付随計算。補題単位の一般化・切り出しは段2の前に再確認'
 elif part=='Operad':cl='E∞の一般論';basis='一般の対称dg operad・代数・自由忘却・模型の移送。HAの∞-operadとの整流比較や必要性は未確定'
 else:cl='一般';basis='複体・単体集合・相対圏・模型圏の一般部品。主用途による段0分類、宣言単位の最終分類は未検収'
 classrows.append(dict(path=str(rel),module=str(rel.with_suffix('')).replace('/','.'),family=part,classification=cl,stage1='stage1 move' if str(rel) in s1old else 'stage2 paper only',lines=len(p.read_text().splitlines()),basis=basis))
with (out/'stage2-classification.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(classrows[0]));w.writeheader();w.writerows(classrows)
assert len(classrows)==2621
# Branch impact: immutable git refs only, include drafts, qualified/partially-qualified names.
changed=[r for r in rows if r['action']=='move'];needle=set(r['old_module'] for r in changed)
for d in groups:needle.update(['SerrePositivity.EInfinity.'+d,'EInfinity.'+d,d+'.'])
for r in changed:
 if r['id']=='OE05':needle.add(r['old_module'].split('.')[-1])
regex=re.compile('|'.join(re.escape(s) for s in sorted(needle,key=len,reverse=True)))
branches={}
for branch in ['math/inf-supply','codex/bulk-5inf3a','math/scheme','math/bs-impl','codex/g12-monad-catalog']:
 head=git('rev-parse',branch);paths=sorted(set(git('log','--format=','--name-only','--diff-filter=AM',base+'..'+head,'--','*.lean').splitlines()));hits=[]
 for p in paths:
  if not p:continue
  r=subprocess.run(['git','show',head+':'+p],capture_output=True,text=True)
  if r.returncode:continue
  hs=sorted(set(regex.findall(r.stdout)))
  if hs:hits.append(dict(path=p,matches=hs,source_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),is_draft=p.startswith('drafts/')))
 branches[branch]=dict(head=head,touched_lean_files=len(paths),affected_files=len(hits),files=hits)
impact=dict(base=base,policy='immutable branch HEAD source files touched by commits not reachable from baseline; exact old module/qualified or partially-qualified namespace/unique BE module basename strings; includes drafts; unqualified declaration references require compiler collection',branches=branches,total_affected_files=sum(b['affected_files'] for b in branches.values()))
(out/'branch-impact.json').write_text(json.dumps(impact,ensure_ascii=False,indent=2)+'\n')
# Static import scope; do not mutate any sources.
mm={r['old_module']:r['new_module'] for r in rows};imports=[];down=[]
for p in sorted((root/'SerrePositivity').rglob('*.lean')):
 im=re.findall(r'^(?:public\s+|private\s+|meta\s+)?import\s+(\S+)',p.read_text(),re.M);hit=sorted(set(im)&{r['old_module'] for r in changed})
 if hit and str(p.relative_to(root)) not in {r['old_path'] for r in rows}:down.append(dict(path=str(p.relative_to(root)),imports=hit))
for r in rows:
 im=re.findall(r'^(?:public\s+|private\s+|meta\s+)?import\s+(\S+)',(root/r['old_path']).read_text(),re.M)
 for m in im:
  if m.startswith('SerrePositivity.EInfinity.') and m not in mm:imports.append(dict(source=r['old_module'],target=m,new_source=r['new_module'],note='outside move set; keep existing dependency and compare layer baseline'))
(out/'static-imports.json').write_text(json.dumps(dict(external_importers=down,retained_einfinity_imports=imports),ensure_ascii=False,indent=2)+'\n')
stats=dict(base=base,stage1_files=len(rows),stage1_move=sum(r['action']=='move' for r in rows),stage1_keep=sum(r['action']=='keep' for r in rows),stage1_lines=sum(r['lines'] for r in rows),groups={g:dict(files=sum(r['id']==g for r in rows),lines=sum(r['lines'] for r in rows if r['id']==g)) for g in ['OE01','OE02','OE03','OE04','OE05']},stage2_files=len(classrows),stage2_remaining=sum(r['stage1']=='stage2 paper only' for r in classrows),stage2_classes={c:dict(files=sum(r['classification']==c for r in classrows),lines=sum(r['lines'] for r in classrows if r['classification']==c)) for c in ['一般','BE固有','E∞の一般論']},branch_affected=impact['total_affected_files'],external_importers=len(down),retained_einfinity_edges=len(imports))
(out/'stage0-summary.json').write_text(json.dumps(stats,ensure_ascii=False,indent=2)+'\n');print(json.dumps(stats,ensure_ascii=False,indent=2));print('branches',[(b,x['affected_files']) for b,x in branches.items()])
