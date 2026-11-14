from pathlib import Path
import re,json,sys,hashlib,subprocess,collections
R=Path.cwd();D=R/'formalization-plans/stage-ii/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
# Reuse the source declaration inventory, without executing its original inventory job.
s=(R/'formalization-plans/stage-ii/bulk-5inf0/inventory.py').read_text();ns={'R':R,'re':re,'hashlib':hashlib,'code_only':code_only};exec(s[s.index('DECL='):s.index('main={};')],ns);scan=ns['scan']
files={}; moves=[]
def mv(old,new,item,why):
 old='SerrePositivity/'+old+'.lean';new='SerrePositivity/'+new+'.lean';assert (R/old).exists(),old
 if old==new:return
 if old in files:assert files[old]==new;return
 files[old]=new;moves.append({'old_path':old,'new_path':new,'old_module':old[:-5].replace('/','.'),'new_module':new[:-5].replace('/','.'),'item':item,'reason':why})
base='BhattScholze/Semiperfectoid/'
for p in sorted((R/'SerrePositivity'/base).rglob('*.lean')):
 rel=str(p.relative_to(R/'SerrePositivity'));tail=rel[len(base):];name=p.stem
 if tail.startswith('Lci/') or name=='Basic':continue
 if name in ['DiscreteDelta','DiscretePrism','PrismRetract']:group='Discrete'
 elif name.startswith(('RawVariableEnvelope','CompletedTensor')) or name in ['PrismRelationQuotient','PerfectEnvelopeInitial']:group='Lci'
 elif tail=='FiniteEnvelopes/PDCompletionPrism.lean':group='Lci';tail=p.name
 elif name in ['Surjectivity','CompatibleRoot','CompatibleRootPerfectoid','AbsolutelyIntegrallyClosedQuotient'] or tail.startswith('RootEnvelope/'):group='Surjectivity'
 elif name in ['Perfectoidization','PerfectPrismDivision','PerfectPrismDivisionComparison','InitialPrismPerfection','Cor73PrismComparison','SurjectiveQuotientPerfectoidization','Product','CharacteristicP']:group='Perfection'
 else:group='Quasiregular'
 mv(rel[:-5],base+group+'/'+tail[:-5],'B3P-06','R7-4 item-based placement; no Cotangent directory')
mv('BhattScholze/Andre/PowerRootEnvelope/PowerRootPolynomial',base+'Quasiregular/RootFamilies/PowerRootPolynomial','B3P-04','R7-3(c): keep delta-dependent implementation within BS; put beside current RootFamily users')
for name in ['Interface','Excision','IntegralExistence']:
 dest='Derived' if name=='Interface' else name
 mv('BhattScholze/Perfectoidization/Derived/'+name,'BhattScholze/Perfectoidization/Interface/'+dest,'B3P-14' if name!='IntegralExistence' else 'B3P-11','R8-8 or R8-3; split outgoing generic pieces first; E3-dependent existence remains on interface side (R10-5g)')
mv('BhattScholze/Perfectoidization/Derived/RootAdjunction','BhattScholze/Perfectoidization/Construction/RootAdjunction','B3P-14','Ring-only root construction')
mv('EInfinity/Perfectoidization/TheoryInterface','BhattScholze/Perfectoidization/Interface/TheoryInterface','B3P-10','R8-1; retain actual declaration namespace at this move')
for old,new in [('Comparison','Comparison'),('Interface','Definition'),('DerivedCorollary','DerivedCorollary')]:mv('EInfinity/Perfectoidization/'+old,'BhattScholze/Perfectoidization/Interface/CAlg/'+new,'B3P-10','Coordinator §5 exception: mechanical move, preserve all names, types and proofs; no deletion')
mv('BhattScholze/Perfectoid/FiniteProduct','BhattScholze/Prism/Perfectoid/FiniteProduct','B3P-14','R8-8 classical perfectoid input beside perfect-prism equivalence')
mv('BhattScholze/Almost/SupportedQuotient','BhattScholze/Perfectoidization/SupportedQuotient','B3P-17','R10-5(a): beside ExcisionTor; keep E3-dependent use outside Almost')
mv('BhattScholze/IntegralPerfectoidization/Completion/IntegralClosureCompletion','BhattScholze/Almost/IntegralClosureCompletion','B3P-20','R10-5(g): align with FiniteEtaleComparison for §10 input')
mv('BhattScholze/IntegralPerfectoidization/Approximation/IntegralApproximation','CommutativeAlgebra/IntegralApproximation/FilteredAlgebra','B3P-20','R10-5(g): pure commutative algebra, use ring-only category interface')
# Explicit outgoing declarations or source sections; these are not whole-module maps.
iface='SerrePositivity/BhattScholze/Perfectoidization/Derived/Interface.lean';inv=scan(R/iface)
setup=[x for x in inv['declarations'] if 53<=x['line']<93]
completion=[x for x in inv['declarations'] if 197<=x['line']<415 and x['leaf'] not in ['restrictCone','restrictCone_vertex','targetDiagram_restriction','targetDiagram_extension','completionRestrictCone','completionExtendCone','completionRestrictCone_vertex','completionExtendCone_vertex']]
splits=[{'item':'B3P-01','old_path':iface,'new_path':'SerrePositivity/HomologicalAlgebra/DerivedCompletion/RingCategories.lean','declarations':[x['name'] for x in setup],'names':'unchanged','note':'9 ordinary category declarations; two nerve abbreviations stay in interface'}, {'item':'B3P-01','old_path':iface,'new_path':'SerrePositivity/HomologicalAlgebra/DerivedCompletion/RingInterface.lean','declarations':[x['name'] for x in completion],'names':'unchanged','note':'Ordinary completion and target-equivalence algebra; retain all nerve and cone declarations in interface; reuse existing RingCompletion'}, {'item':'B3P-11','old_path':'SerrePositivity/BhattScholze/Perfectoidization/Derived/IntegralExistence.lean','new_path':'SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/InitialValueCone.lean','source_section':'InitialLimit','names':'preserve canonical names for first move; exact declaration ownership map completed by native v3b snapshot'}, {'item':'B3P-11','old_path':'SerrePositivity/BhattScholze/Perfectoidization/Derived/IntegralExistence.lean','new_path':'SerrePositivity/BhattScholze/Perfectoidization/Interface/InitialBridge.lean','source_section':'InitialBridge','names':'unchanged'}, {'item':'B3P-03','old_path':'SerrePositivity/BhattScholze/Andre/Envelope/RootSource.lean','new_path':'SerrePositivity/HomologicalAlgebra/DerivedCompletion/IteratedPDH0.lean','source_section':'IteratedPDH0Reflection','names':'move generic reflection comparison into DerivedCompletion; native snapshot fills generated/private rules'}, {'item':'B3P-18','old_path':'SerrePositivity/BhattScholze/Andre/Transfinite/Limit.lean','new_path':'SerrePositivity/CommutativeAlgebra/Reduced/PowerAnnihilator.lean','declarations':['SerrePositivity.BhattScholze.Andre.Transfinite.mul_eq_zero_of_pow_mul_eq_zero_of_reduced'],'new_namespace':'SerrePositivity.CommutativeAlgebra'}]
splits[0]['declarations'] += ['SerrePositivity.BhattScholze.PerfectoidizationInterface.'+n for n in ['targetUnitMap','targetUnitMap_naturality','quotientAlgebra','quotientProjection','quotientComparison','quotientSquare_commutes','ArcOutside']]
splits[0]['note']='16 ordinary category, target-unit, quotient and valuation-extension declarations; nerves and simplicial squares stay in BS'
splits.append({'item':'B3P-03','old_path':'SerrePositivity/BhattScholze/Andre/Envelope/DivisionResidue.lean','new_path':'SerrePositivity/BhattScholze/Delta/Division/AdjoinResidue.lean','declarations':['SerrePositivity.BhattScholze.'+n for n in ['deltaAdjoinDivisionResidueIdeal','DeltaAdjoinDivisionResidue','deltaAdjoinDivisionResidueIdeal_eq_map','deltaAdjoinDivisionResidueSupEquiv','deltaAdjoinDivisionResidueSupEquiv_mk','deltaAdjoinDivisionResidueSupEquiv_coeff','deltaDivisionSourceResidueTargetAlgebra','deltaDivisionSourceResidueTargetAlgebra_algebraMap','deltaDivisionSourceTensor_residueIdeal_map','deltaDivisionSourceResidueTensorEquiv','deltaDivisionSourceResidueTensorEquiv_tmul','deltaDivisionSourceResidueTensorAlgEquiv']],'names':'unchanged','note':'Extract raw delta residue and tensor presentation only. Retain Normalized-dependent flatness/regularity in Andre, avoiding new Delta->Andre reverse edges.'})
all_candidates=set(files)|{str(p.relative_to(R)) for p in (R/'SerrePositivity/BhattScholze/Semiperfectoid').rglob('*.lean')}|{str(p.relative_to(R)) for p in (R/'SerrePositivity/BhattScholze/Almost').rglob('*.lean')}|{str(p.relative_to(R)) for p in (R/'SerrePositivity/BhattScholze/PerfectoidIdeal').rglob('*.lean')}|{str(p.relative_to(R)) for p in (R/'SerrePositivity/BhattScholze/Andre/Envelope').glob('*.lean')}|{x['old_path'] for x in splits}
names=[];inventory=[]
for f in sorted(all_candidates):
 info=scan(R/f);inventory.append(info)
 for x in info['declarations']:
  old=x['name']
  if not old or x['private']:continue
  new=old;owner=files.get(f,f)
  if '/Semiperfectoid/' in f:
   # Methods remain in the actual structure namespace; do not manufacture a module namespace.
   keep=any(old.startswith(z) for z in ['SerrePositivity.BhattScholze.OrientedPrism.','SerrePositivity.BhattScholze.DeltaStructure.','SerrePositivity.BhattScholze.Prismatic.PrismOver.','SerrePositivity.BhattScholze.Inputs.'])
   if not keep:
    for prefix in ['SerrePositivity.BhattScholze.Semiperfectoid.','SerrePositivity.BhattScholze.Prismatic.','SerrePositivity.BhattScholze.','SerrePositivity.']:
     if old.startswith(prefix):new='SerrePositivity.BhattScholze.Semiperfectoid.'+old[len(prefix):];break
  elif f.endswith('/PowerRootPolynomial.lean'):
   new=old.replace('SerrePositivity.BhattScholze.Andre.','SerrePositivity.BhattScholze.Semiperfectoid.',1)
  elif '/Andre/Envelope/' in f and not f.endswith('DivisionResidue.lean'):
   if old.startswith('SerrePositivity.BhattScholze.') and not old.startswith(('SerrePositivity.BhattScholze.Andre.','SerrePositivity.BhattScholze.OrientedPrism.','SerrePositivity.BhattScholze.DeltaStructure.')):new=old.replace('SerrePositivity.BhattScholze.','SerrePositivity.BhattScholze.Andre.',1)
  elif f.endswith('SupportedQuotient.lean'):
   new=old.replace('SerrePositivity.BhattScholze.','SerrePositivity.BhattScholze.Perfectoidization.',1)
  elif '/Almost/' in f:
   if not old.startswith('SerrePositivity.BhattScholze.Almost.') and old.startswith('SerrePositivity.BhattScholze.'):new=old.replace('SerrePositivity.BhattScholze.','SerrePositivity.BhattScholze.Almost.',1)
  elif '/PerfectoidIdeal/' in f and old.startswith('SerrePositivity.') and not old.startswith('SerrePositivity.BhattScholze.'):
   new=old.replace('SerrePositivity.','SerrePositivity.BhattScholze.Almost.',1)
  elif f.endswith('/IntegralClosureCompletion.lean'):new=old.replace('SerrePositivity.BhattScholze.Perfectoidization.Derived.','SerrePositivity.BhattScholze.Almost.',1)
  elif f.endswith('/IntegralApproximation.lean'):new=old.replace('SerrePositivity.BhattScholze.Perfectoidization.Derived.','SerrePositivity.CommutativeAlgebra.',1)
  if new.endswith('.perfectoidIdeal_radical'):new=new[:-len('perfectoidIdeal_radical')]+'perfectoidKernel_radical'
  if new.endswith('.IsJAlmostZero'):new=new[:-len('IsJAlmostZero')]+'IsAlmostZeroComplex'
  for split in splits:
   selected=old in split.get('declarations',[])
   if split['old_path']==f and split.get('source_section')=='InitialLimit':selected=x['line']<238
   if split['old_path']==f and split.get('source_section')=='InitialBridge':selected=250<=x['line']<406
   if split['old_path']==f and split.get('source_section')=='IteratedPDH0Reflection':selected=1462<=x['line']<1592
   if split['old_path']==f and selected:
    owner=split['new_path']
    if split.get('source_section')=='InitialLimit':new=old.replace('SerrePositivity.BhattScholze.PerfectoidizationInterface.','SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.',1)
    elif split.get('source_section')=='IteratedPDH0Reflection':new=old.replace('SerrePositivity.BhattScholze.','SerrePositivity.DerivedCompletion.',1)
    elif split.get('new_namespace'):new=split['new_namespace']+'.'+old.rsplit('.',1)[-1]
    else:new=old
  if new!=old or owner!=f:names.append({'old':old,'new':new,'old_module':f[:-5].replace('/','.'),'new_module':owner[:-5].replace('/','.'),'source_line':x['line'],'kind':x['kind']})
collisions=[{'target':v,'sources':ks} for v,ks in ((v,[k for k,w in files.items() if w==v]) for v in set(files.values())) if len(ks)>1 or (R/v).exists() and v not in files]
bynew=collections.defaultdict(list)
for n in names:bynew[n['new']].append(n['old'])
name_collisions={k:sorted(set(v)) for k,v in bynew.items() if len(set(v))>1}
wr=lambda name,data:(D/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
wr('module-map.proposed.json',{'status':'stage0 source proposal; not applied','baseline':'32d364b53','rows':moves})
wr('namespace-map.proposed.json',{'status':'source-declared public names only; native kernel export must add generated and private rules before application','rows':names,'source_target_collisions':name_collisions})
wr('split-plan.proposed.json',{'status':'stage0 proposal; dependency closures and exact native ownership to be validated before application','rows':splits})
wr('source-inventory.json',{'status':'syntactic source inventory, not a Lean environment snapshot','files':inventory})
wr('stage0-map-check.json',{'whole_moves':len(moves),'split_outputs':len(splits),'public_source_rows':len(names),'changed_public_source_names':sum(x['old']!=x['new'] for x in names),'path_collisions':collisions,'source_name_collisions':name_collisions,'note':'Existing unchanged declarations and compiler-generated names are checked against actual Lean environments during preparation; this is not a preservation result.'})
print('whole moves',len(moves),'split outputs',len(splits),'public source rows',len(names),'renames',sum(x['old']!=x['new'] for x in names),'path collisions',len(collisions),'source name collisions',len(name_collisions))
