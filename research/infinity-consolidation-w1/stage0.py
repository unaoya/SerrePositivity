#!/usr/bin/env python3
"""IC-1 紙のソース分析。Lean/build/native採取・移動は実行しない。"""
from pathlib import Path
import sys,re,json,csv,subprocess,hashlib,collections
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts/refactor'))
from layer_check import imports as full_imports,code_only
def imports(s):
    matches=list(re.finditer(r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[^\n]*",s))
    if not matches:return set()
    try:return full_imports(s[:matches[-1].end()])
    except ValueError:return full_imports(s)
sys.path.insert(0,str(ROOT/'evidence/consolidation/organize-einfinity-w1/preparation-code'))
from source_names import declarations
OUT=Path(__file__).resolve().parent

def git(*args,cwd=ROOT): return subprocess.check_output(['git',*args],cwd=cwd,text=True).strip()
def dump(name,obj): (OUT/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
def table(name,rows):
    if not rows:return
    with (OUT/name).open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
def module(p):return p[:-5].replace('/','.')
paths=git('ls-files','*.lean').splitlines()
src={p:(ROOT/p).read_text() for p in paths if (ROOT/p).exists()}
import pickle
cache=Path('/private/tmp/ic-w1-stage0-graph.pickle')
key=hashlib.sha256(''.join(p+hashlib.sha256(s.encode()).hexdigest() for p,s in src.items()).encode()).hexdigest()
if cache.exists() and (cached:=pickle.loads(cache.read_bytes()))[0]==key: graph=cached[1]
else:
    graph={module(p):imports(s) for p,s in src.items()}
    cache.write_bytes(pickle.dumps((key,graph)))
rev=collections.defaultdict(set)
for m,ds in graph.items():
    for d in ds:rev[d].add(m)
def closure(starts,g):
    seen=set(starts); todo=list(starts)
    while todo:
        for d in g.get(todo.pop(),()):
            if d not in seen:seen.add(d);todo.append(d)
    return seen
family_dest={
'AlexanderWhitney':'HomologicalAlgebra/SimplicialChains/AlexanderWhitney',
'CosimplicialNormalization':'HomologicalAlgebra/Cosimplicial/Normalization',
'DGAlgebra':'DifferentialGraded/Algebras',
'ComplexLimits':'HomologicalAlgebra/Complexes/Limits',
'Hammock':'InfinityCategories/HA/ModelCategoryComparison/Hammock',
'HomologyZero':'HomologicalAlgebra/Complexes/HomologyZero',
'NatTensor':'HomologicalAlgebra/Complexes/NatTensor',
'NegativeTensor':'HomologicalAlgebra/Complexes/NegativeTensor',
'Shuffle':'HomologicalAlgebra/SimplicialChains/Shuffle',
'Operad':'InfinityCategories/Models/EInfinity/DGOperads',
}
be={'BergerFresse','IntervalCuts','SimplexCuts','Surjection','TableReduction'}
standalone={'FrameRealizationLifting.lean':'HomotopicalAlgebra/HomotopyFunctionComplex/FrameRealizationLifting.lean',
'HomBiprodRestriction.lean':'HomologicalAlgebra/Complexes/HomBiprodRestriction.lean','HomHomotopy.lean':'HomologicalAlgebra/Complexes/HomHomotopy.lean','HomRestriction.lean':'HomologicalAlgebra/Complexes/HomRestriction.lean',
'NativeBinaryCoconeHom.lean':'HomologicalAlgebra/Complexes/NativeBinaryCoconeHom.lean','OppositeFactorization.lean':'HomotopicalAlgebra/ModelCategory/OppositeFactorization.lean',
'ProjectiveCofibrantUnit.lean':'HomotopicalAlgebra/Complexes/ProjectiveCofibrantUnit.lean','ProjectiveCofibration.lean':'HomotopicalAlgebra/Complexes/ProjectiveCofibration.lean','ProjectiveHomotopyInverse.lean':'HomotopicalAlgebra/Complexes/ProjectiveHomotopyInverse.lean','ProjectiveModel.lean':'HomotopicalAlgebra/Complexes/ProjectiveModel.lean','StrictAdjunctionBar.lean':'HomotopicalAlgebra/Bar/StrictAdjunctionBar.lean'}
old=list(csv.DictReader((ROOT/'evidence/consolidation/organize-einfinity-w1/stage2-classification.csv').open()))
rows=[];declrows=[];prefixes={}
for r in old:
    p=r['path']
    if p not in src:continue # OE-W1 stage1済み357本を除外
    rel=p.split('EInfinity/',1)[1];fam=r['family']
    if fam in be:dest='InfinityCategories/Models/EInfinity/BarrattEccles/'+rel
    elif fam in family_dest:dest=family_dest[fam]+rel[len(fam):]
    else:dest=standalone[rel]
    new='SerrePositivity/'+dest
    # MathlibのHomotopicalAlgebraを隠さない主題namespace
    ns_old='SerrePositivity.EInfinity.'+(fam if '/' in rel else Path(rel).stem)
    if fam in be: ns_new='SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.'+fam
    elif fam=='Operad':ns_new='SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads'
    elif fam=='Hammock':ns_new='SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock'
    else:ns_new='SerrePositivity.'+({'AlexanderWhitney':'SimplicialChains.AlexanderWhitney','Shuffle':'SimplicialChains.Shuffle','ComplexLimits':'ComplexLimits','DGAlgebra':'DGAlgebra','CosimplicialNormalization':'CosimplicialNormalization'}.get(fam,Path(fam).stem))
    prefixes[ns_old]=ns_new
    ds=declarations(src[p],p)
    n=0
    for name,_,line in ds:
        prefix=ns_old if name==ns_old or name.startswith(ns_old+'.') else 'SerrePositivity.EInfinity'
        changed=ns_new+name[len(prefix):] if name==prefix or name.startswith(prefix+'.') else name
        if fam=='Operad' and name.startswith('SerrePositivity.EInfinity'):
            changed=ns_new+name[len('SerrePositivity.EInfinity'):]
        n+=changed!=name
        declrows.append(dict(old_name=name,new_name=changed,path=p,line=line,status='source hint; native ownership pending'))
    rows.append(dict(id='IC1-'+fam,old_path=p,new_path=new,old_module=module(p),new_module=module(new),family=fam,classification=r['classification'],lines=r['lines'],old_namespace_prefix=ns_old,new_namespace_prefix=ns_new,source_named_candidates=len(ds),source_rename_candidates=n,sha256=hashlib.sha256(src[p].encode()).hexdigest()))
table('moves.csv',rows);table('source-name-hints.csv',declrows)
move={r['old_module']:r['new_module'] for r in rows}
prefixes['SerrePositivity.EInfinity.Operad']='SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad'
prefixes['file_owned_rule_note']='Operad/のroot EInfinity所有宣言はDGOperads直下、Operad型とそのメソッドはDGOperads.Operad。全EInfinityの文字列置換には使用不可。standaloneを含む全ての正式対応はsource-name-hints.csvとnative所有元を照合してから。'
dump('namespace-prefix-proposal.json',prefixes)
# branch/worktree read-only: commits main..branch + dirty/untracked
lanes={}
for branch,dirname in [('math/inf-supply','SerrePositivity-bs-classical'),('math/scheme','SerrePositivity-scheme')]:
    wt=ROOT.parent/dirname
    touched=set(git('diff','--name-only','main...'+branch,'--','*.lean').splitlines())
    # include all files touched by unmerged commits (even reverted at tip)
    touched.update(git('log','--format=','--name-only','main..'+branch,'--','*.lean').splitlines())
    dirty=set(git('diff','HEAD','--name-only','--','*.lean',cwd=wt).splitlines())
    dirty.update(git('ls-files','--others','--exclude-standard','*.lean',cwd=wt).splitlines());touched|=dirty;touched.discard('')
    hits=[];kst=[]
    for p in sorted(touched):
        f=wt/p
        if not f.exists():continue
        s=f.read_text();im=imports(s);matched=sorted(im&move.keys())
        masked=code_only(s);names=[k for k in prefixes if k in masked]
        if matched or names or module(p) in move:hits.append(dict(path=p,imports=matched,namespace_prefixes=names))
        if any(d.startswith('SerrePositivity.KST') for d in im):kst.append(dict(path=p,imports=sorted(d for d in im if d.startswith('SerrePositivity.KST'))))
    lanes[branch]=dict(head=git('rev-parse',branch),worktree=str(wt),touched_lean=len(touched),dirty_lean=sorted(dirty),affected_files=len(hits),affected_imports=sum(len(x['imports']) for x in hits),hits=hits,kst_importers=kst,touched_paths=sorted(touched),readable_touched=sum((wt/p).exists() for p in touched))
dump('branch-impact.json',lanes)
# root closure / audit outsiders
root=closure(['SerrePositivity'],graph)
auditpaths=[p.strip() for p in (ROOT/'scripts/refactor/audit_manifest.txt').read_text().splitlines() if p.strip() and not p.startswith('#')]
auditroots=set().union(*(graph.get(module(p),set()) for p in auditpaths))
aud=closure(auditroots,graph)
outs=sorted((aud-root)&set(graph));table('root-outside-audit.csv',[dict(module=m,path=m.replace('.','/')+'.lean',ic1=m in move,area=m.split('.')[1] if '.' in m else '') for m in outs])
# DG: actual infinity declarations vs mere algebraic resolution, all files accounted
DG=[]
for p,s in src.items():
    if not (p.startswith('SerrePositivity/DifferentialGraded/') or p=='SerrePositivity/DifferentialGraded.lean'):continue
    clean=code_only(s); hits=re.findall(r'\b(?:dgNerve\w*|differentialGradedNerve\w*|QCat\w*|Quasicategory\w*|InfinityCategory\w*)\b',clean)
    c='Checks据置' if '/Checks/' in p else ('∞接点・要個別分離' if hits else 'dg理論据置')
    DG.append(dict(path=p,module=module(p),lines=len(s.splitlines()),classification=c,destination=p,coverage_items='Kerodon 2.5（∞接点候補のみ・個別番号未同定）' if hits else '',external_importers=sum(not m.startswith('SerrePositivity.DifferentialGraded.') for m in rev[module(p)]),basis='code tokens: '+','.join(sorted(set(hits))) if hits else 'dgの通常圏・複体・分解の構成。semifreeという語だけでは∞模型へ移さない'))
table('dg-classification.csv',DG)
# choose: transfer exact 255 judgements, source provenance
prior=ROOT.parent/'SerrePositivity-bs-classical/formalization-plans/stage-ii/inf-supply-choose-1117.json'
a=json.loads(prior.read_text());dump('choose-inherited.json',{k:([{kk:vv for kk,vv in x.items() if kk!='original_choice_source'} for x in v] if k=='definitions' else v) for k,v in a.items()})
covered={(x['file'],x['source_name']) for x in a['definitions']}
newchoices=[];unassigned=[]
for p,s in src.items():
    if not p.startswith(('SerrePositivity/InfinityCategories/','SerrePositivity/EInfinity/')):continue
    clean=code_only(s)
    # all source declarations, including theorem/local/anonymous fallback for coverage
    pat=r'(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe|local|scoped|partial)\s+)*(def|abbrev|theorem|lemma|opaque|instance|example|structure|class|inductive)\b\s*([^\s(:{]+)?'
    bounds=list(re.finditer(pat.replace(r'\s+',r'[ \t]+').replace(r'\s*',r'[ \t]*'),clean)); positions=list(re.finditer(r'\bClassical\.(?:choose|choice)\b|(?<![\w])(?:Exists\.choose)\b|\.choose\b',clean))
    for m in positions:
        prev=next((b for b in reversed(bounds) if b.start()<=m.start()),None)
        if prev is None:unassigned.append(dict(path=p,line=clean.count('\n',0,m.start())+1));continue
        name=prev[2] or '<anonymous>';kind=prev[1]
        if (p,name) in covered:continue
        key=(p,name,prev.start())
        if any(x['_key']==key for x in newchoices):continue
        end=next((b.start() for b in bounds if b.start()>prev.start()),len(s));body=s[prev.start():end];masked_body=clean[prev.start():end]
        # only data-producing definitions; proofs logged separately for exhaustiveness
        newchoices.append(dict(_key=key,file=p,source_name=name,kind=kind,line=clean.count('\n',0,prev.start())+1,selection_lines=[raw.strip() for raw,masked in zip(body.splitlines(),masked_body.splitlines()) if re.search(r'choose|choice',masked)],existence_references=sorted(set(re.findall(r'\b(?:exists_|nonempty_|hasColimit_|hasLimit_|trivialKanFibration_exists_)\w+',masked_body))),transitive_importers=len(closure([module(p)],rev))-1,other_lanes=[b for b,l in lanes.items() if p in l['touched_paths']],original_source=body))
for i,x in enumerate(newchoices,1):x.pop('_key');x['id']=f'ICCH{i:03}'
dump('choose-new-candidates.json',dict(method='comment/string masked; declaration boundary scan, all .choose including typeclass APIs; source only',definitions=newchoices,unassigned=unassigned))
# content by chapter and B1 leaf candidates (no direct project importer = graph leaf)
contents=collections.Counter();small=[]
for p,s in src.items():
    if not p.startswith('SerrePositivity/InfinityCategories/'):continue
    parts=p.split('/');contents['/'.join(parts[2:-1])]+=1
    m=module(p);lines=len(s.splitlines())
    if lines<=80 and not rev[m]:small.append(dict(path=p,chapter='/'.join(parts[2:-1]),lines=lines,direct_importers=0))
table('infinity-content.csv',[dict(directory=k,files=v) for k,v in sorted(contents.items())]);table('b1-leaf-candidates.csv',small)
tiers=json.loads((ROOT/'scripts/refactor/layers.json').read_text())['klw1']['modules']
full_ic=[dict(path=p,module=module(p),lines=len(s.splitlines()),content='/'.join(p.split('/')[2:-1]),tier=tiers.get(module(p),'未登録'),native_owner='未採取') for p,s in src.items() if p.startswith('SerrePositivity/InfinityCategories/')]
table('infinity-files.csv',full_ic)
summary=dict(infinity_files=len(full_ic),infinity_lines=sum(r['lines'] for r in full_ic),head=git('rev-parse','HEAD'),main=git('rev-parse','main'),source_files=len(src),moves=len(rows),families=dict(collections.Counter(r['family'] for r in rows)),classifications=dict(collections.Counter(r['classification'] for r in rows)),source_name_hints=len(declrows),source_rename_hints=sum(r['old_name']!=r['new_name'] for r in declrows),destination_collisions=[r['new_path'] for r in rows if r['new_path'] in src],duplicate_destinations=[k for k,v in collections.Counter(r['new_path'] for r in rows).items() if v>1],external_importers=len({m for m,ds in graph.items() if m not in move and ds&move.keys()}),root_project=len(root&set(graph)),audit_outside_root=len(outs),ic1_outside_root=sum(m in move for m in outs),dg=dict(collections.Counter(r['classification'] for r in DG)),inherited_choices=len(a['definitions']),new_choice_kinds=dict(collections.Counter(x['kind'] for x in newchoices)),unassigned_choices=unassigned,b1_small_graph_leaves=len(small),choose_source_sha256=hashlib.sha256(prior.read_bytes()).hexdigest())
dump('summary.json',summary);print(json.dumps(summary,ensure_ascii=False,indent=2))
