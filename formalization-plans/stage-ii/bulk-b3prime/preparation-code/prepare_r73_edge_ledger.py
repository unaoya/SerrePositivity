from pathlib import Path
import json
W=Path('/tmp/bulk-b3prime');prefix='SerrePositivity.BhattScholze.';rows=[]
items=[
 ('Semiperfectoid.Lci.LciEnvelopeCompletedResidue','Andre.Transfinite.Colimit',['SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition','SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion'],'redirect to generic owners already in baseline B3'),
 ('Semiperfectoid.Lci.LciEnvelopeCompletedResidueFaithful','Andre.Transfinite.Colimit',['SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition','SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion'],'redirect to generic owners already in baseline B3'),
 ('Semiperfectoid.RootFamilyBase','Andre.Transfinite.Colimit',['SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons'],'redirect to actual HA defining module; preserve actual declaration namespace'),
 ('Semiperfectoid.RootFamilyBase','Andre.PowerRootEnvelope.PowerRootPolynomial',[prefix+'Semiperfectoid.Quasiregular.RootFamilies.PowerRootPolynomial'],'whole-module relocation'),
 ('Semiperfectoid.Lci.LciEnvelopePresentation','Andre.Envelope.DivisionResidue',[prefix+'Andre.Envelope.DivisionResidue'],'retained: faithful-flatness theorem depends on Normalized and ordinary root/monic input; moving the entire owner into Delta would create Delta -> Andre reverse dependency/cycle; extract only the 12 source-independent raw-residue/tensor declarations'),
 ('Semiperfectoid.Lci.LciEnvelopeRegular','Andre.Envelope.RootSource',['SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedPDH0'],'redirect to extracted generic section with unchanged type/proof'),
 ('Semiperfectoid.Lci.LciEnvelopeKoszul','Andre.OrdinaryRoots.MonicRelation',['SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation'],'already resolved in baseline B3'),
 ('Semiperfectoid.RootRelationPolynomial','Andre.OrdinaryRoots.MonicRelation',['SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation'],'already resolved in baseline B3')]
for importer,old,targets,decision in items:
 m=prefix+importer;p=W/'before'/('refs-'+m)/(m+'.json');refs=[]
 if p.exists():
  data=json.loads(p.read_text());refs=sorted({(r['module'],r['name']) for r in data['refs'] if r.get('name') and '.Andre.' in r.get('module','') and r['kind'] not in ['binder','local']})
 rows.append({'original_importer':m,'original_import':prefix+old,'target_owners':targets,'decision':decision,'native_original_Andre_references':[{'module':owner,'name':name} for owner,name in refs]})
(W/'r7-3b-edge-ledger.json').write_text(json.dumps({'status':'source/import preparation; actual final target build and v3b required; no claim every reverse edge disappears','review_edges':8,'already_baseline':2,'planned_resolution_in_bundle':5,'retained':1,'rows':rows},ensure_ascii=False,indent=2));print('R7-3b edges8: baseline2, planned resolution5, retained1')
