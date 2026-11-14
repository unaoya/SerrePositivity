from pathlib import Path
import json,re,sys,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');D=R/'formalization-plans/stage-ii/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
status=json.loads((W/'rewrite-status.json').read_text());before=json.loads((W/'before-manifest.json').read_text());required=set(before['reference_files']);ready=set(status['files']);assert not status['review'],status['review'];assert ready==required,{'missing':sorted(required-ready),'extra':sorted(ready-required)};assert (W/'before/complete.json').exists(),'original-environment captures incomplete'
plan=json.loads((W/'namespace-rewrite-plan.json').read_text());splitplan=json.loads((W/'split-bundle/plan.json').read_text());assert len(splitplan['records'])==5;modulemap=plan['modules'];surrogates={'SerrePositivity.Inputs.Perfectoidization':'SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence'};allimports=modulemap|surrogates;closure=json.loads((D/'stage0-import-closure.json').read_text())['reverse_closure'];out=W/'final-bundle';out.mkdir(exist_ok=True);files={};deleted=set();audit=[]
# Match the existing collector's import grammar, altering only the module token.
rx=re.compile(r'(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\s+(?:all\s+)?([^\W\d][\w\']*(?:\.[^\W\d][\w\']*)*)')
def imports(text):
 mask=code_only(text)
 for match in reversed(list(rx.finditer(mask))):
  old=match[1]
  if old in allimports:a,b=match.span(1);text=text[:a]+allimports[old]+text[b:]
 return text
for m in closure:
 p=m.replace('.','/')+'.lean';target=modulemap.get(m,m)
 if m in surrogates:deleted.add(p);continue
 if p in status['files']:
  row=status['files'][p];text=(W/'rewritten'/row['target']).read_text();assert hashlib.sha256(text.encode()).hexdigest()==row['preview_sha256']
 else:text=imports((R/p).read_text())
 text=imports(text)
 if target in splitplan['files']:text=(W/'split-bundle'/(target.replace('.','/')+'.lean')).read_text();assert hashlib.sha256(text.encode()).hexdigest()==splitplan['files'][target]
 if target!=m:deleted.add(p)
 files[target]=text
for m,sha in splitplan['files'].items():
 p=W/'split-bundle'/(m.replace('.','/')+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==sha;files[m]=p.read_text()
# Preserve the exact original Finite parameter telescope. The compatibility
# theorem was the only consumer of the finite-presentation section instance.
# `include` does not force unused section hypotheses into definitions; give the
# original full telescope explicitly, keeping the value and all argument order.
m='SerrePositivity.BhattScholze.Perfectoidization.Finite';text=files[m];old='noncomputable def Perfectoidization : Type u :=';assert text.count(old)==1
head='noncomputable def Perfectoidization (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]\n    [Module.Finite R S] [Algebra.FinitePresentation R S]\n    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) : Type u :='
files[m]=text.replace(old,head)
# Ring-only users must import the ordinary algebra interface, including newly moved CA owner.
for row in json.loads((W/'r82-consumers.json').read_text()):
 m=row['path'][:-5].replace('/','.');dest=modulemap.get(m,m);text=files[dest];old='public import '+modulemap['SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface'];new='public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingInterface';assert text.count(old)==1,(dest,old);files[dest]=text.replace(old,new)
# The two §10 consumers need only the extracted elementary reduced-ring lemma.
for m in ['SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison','SerrePositivity.BhattScholze.IntegralPerfectoidization.Completion.IntegralClosureCompletion']:
 dest=modulemap.get(m,m);text=files[dest];old='public import SerrePositivity.BhattScholze.Andre.Transfinite.Limit';assert text.count(old)==1,dest;files[dest]=text.replace(old,'public import SerrePositivity.CommutativeAlgebra.Reduced.PowerAnnihilator\npublic import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion'+('\npublic import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons' if m.endswith('.IntegralClosureCompletion') else ''))
# Removing a broad derived interface also removes an accidental Mathlib
# transitive import needed by this downstream valuation proof. Use its actual
# original native defining module, not a replacement construction.
m='SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationExtension';line='public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure\n';assert line not in files[m];files[m]=files[m].replace('module\n','module\n'+line,1)
# R7-3(b): use the actual already-extracted generic owners rather than the
# Andre aggregate that happened to re-export them. Mathematical terms unchanged.
for oldmod,replacements in {
 'SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeCompletedResidue':{'SerrePositivity.BhattScholze.Andre.Transfinite.Colimit':['SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition','SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion']},
 'SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeCompletedResidueFaithful':{'SerrePositivity.BhattScholze.Andre.Transfinite.Colimit':['SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition','SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion']},
 'SerrePositivity.BhattScholze.Semiperfectoid.RootFamilyBase':{'SerrePositivity.BhattScholze.Andre.Transfinite.Colimit':['SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons']},
 'SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeRegular':{'SerrePositivity.BhattScholze.Andre.Envelope.RootSource':['SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedPDH0']}
}.items():
 m=modulemap.get(oldmod,oldmod);text=files[m]
 for old,targets in replacements.items():
  line='public import '+old;assert text.count(line)==1,(m,old);text=text.replace(line,'\n'.join('public import '+n for n in targets))
 files[m]=text
# BS-specific specializations belong in the BS aggregate, preserving all declaration names.
einf='SerrePositivity.EInfinity';bs='SerrePositivity.BhattScholze';bs_special=[r['new_module'] for r in json.loads((D/'module-map.proposed.json').read_text())['rows'] if r['old_module'].startswith('SerrePositivity.EInfinity.Perfectoidization.')];removed=[]
for n in bs_special:
 line='public import '+n
 if line in files[einf]:files[einf]=re.sub(r'(?m)^'+re.escape(line)+r'[ \t]*\n','',files[einf]);removed.append(n)
 assert 'public import '+n not in files[einf]
 for_aggregate='public import '+n+'\n'
 if for_aggregate not in files[bs]:files[bs]+='\n'+for_aggregate
audit.append({'kind':'BS-specific aggregate relocation','modules':bs_special,'removed_from_EInfinity':removed})
# Approved publication of proved alternative endpoints; never delete unused mathematical results.
for row in json.loads((D/'stage0-import-closure.json').read_text())['publication_targets']:
 n=modulemap.get(row['module'],row['module']);line='public import '+n+'\n'
 if line not in files[bs]:files[bs]+='\n'+line
# Comment-only approved scope outside the semantic reverse closure still needs
# native before/after evidence and target builds. Do not invent semantic edits.
for m in json.loads((W/'additional-doc-modules.json').read_text()):
 assert m not in files,m
 text=(R/(m.replace('.','/')+'.lean')).read_text();assert imports(text)==text,('uncollected semantic import edit',m)
 files[m]=text
# Preserve actual canonical namespaces of imported types. No new opens inferred from module paths.
for m,text in files.items():
 p=out/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
full=json.loads((R/'scripts/refactor/layers.json').read_text());oldtiers=dict(full['klw1']['modules']);newtiers=json.loads((D/'new-main-tiers.json').read_text())
for m,row in newtiers.items():assert m not in oldtiers;full['klw1']['modules'][m]=row['tier']
full['klw1']['modules']['SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialValueCone']='Portable';p=out/'scripts/refactor/layers.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(full,ensure_ascii=False,indent=2)+'\n')
manifest={'status':'generated complete source bundle only; not applied or validated','baseline':'32d364b53','files':{m:hashlib.sha256(text.encode()).hexdigest() for m,text in files.items()},'delete_paths':sorted(deleted),'audit':audit,'protected_policy':'EInfinity changes only four approved BS specializations and aggregate imports; no existing InfinityCategories or AlgebraicGeometry Lean edits; new generic Cofinality file permitted.'};(out/'manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n');print('bundle',len(files),'files; deletions',len(deleted))
