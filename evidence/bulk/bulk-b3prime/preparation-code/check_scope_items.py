from pathlib import Path
import json,hashlib
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'evidence/bulk/bulk-b3prime';old=json.loads((D/'stage0-items.json').read_text());mapping=json.loads((W/'B4/module-map.json').read_text());owners=json.loads((W/'B4/public-owner-map.json').read_text())['rows'];manifest=json.loads((W/'final-bundle/manifest.json').read_text());pub=json.loads((W/'actual-import-graph.json').read_text())['publication_targets'];evidence={}
def module(m):return R/(m.replace('.','/')+'.lean')
def add(n,text,files,extra=None):
 for f in files:assert (R/f).is_file(),f
 evidence[n]={'implementation':text,'evidence_files':files,'checks':extra or {}}
p='SerrePositivity/'
add(1,'環のSetup・CompletionをRingCategories/RingInterfaceへ分割。元のinterfaceは神経・錐を保つ。',[p+'HomologicalAlgebra/DerivedCompletion/RingCategories.lean',p+'HomologicalAlgebra/DerivedCompletion/RingInterface.lean',p+'BhattScholze/Perfectoidization/Interface/Derived.lean'])
add(2,'基準mainでMonicRelation・Familyの汎用多項式補題はKoszulRegular。再移動しない。',[p+'CommutativeAlgebra/KoszulRegular/MonicRelation.lean'])
add(3,'八辺は基準解消2・今回解消5・維持1。一般のIteratedPDH0とAdjoinResidueのみ抽出、忠実平坦性のAndre依存は残す。',[p+'HomologicalAlgebra/DerivedCompletion/IteratedPDH0.lean',p+'BhattScholze/Delta/Division/AdjoinResidue.lean'],{'edge_ledger':'r7-3b-edge-ledger.json'})
add(4,'PowerRootPolynomialはDelta依存を保ちSemiperfectoid/Quasiregular/RootFamiliesへ。',[p+'BhattScholze/Semiperfectoid/Quasiregular/RootFamilies/PowerRootPolynomial.lean'])
add(5,'基準mainで存在定理はPrism/Perfectoid。再移動しない。',[p+'BhattScholze/Prism/Perfectoid/PerfectoidPrismPresentation.lean'])
add(6,'Discrete・Lci・Quasiregular・Perfection・Surjectivityに分類。Cotangentは作らない。',[],{'Semiperfectoid_moves':sum('.Semiperfectoid.' in a for a in mapping),'whole_module_map':'B4/module-map.json'})
add(7,'Semiperfectoidの宣言名とディレクトリを揃える。型に属するメソッドは型の実名前空間を保つ。',[],{'owner_table':'B4/public-owner-map.json'})
assert all(r['root_reachable'] for r in pub)
add(8,'RootEnvelope三本・PerfectPrismDivisionComparison・PDivisionSourceを公開。Audit四本は既存scriptsの配置を維持。',[],{'publication_targets':pub,'audit_coverage':'all-audit-inventory.json'})
add(9,'旧見出し・未存在パス・工程ラベル・draftsとの古い比較をコメントだけ訂正。',[],{'comment_receipt':'bundle-docs-receipt.json','old_label_scan':'remaining-old-labels.json'})
add(10,'TheoryInterfaceと承認済みCAlg_R三本をBSへ移動。CAlg_Rは宣言名・型・証明維持。EInfinityからBSへの直接/間接依存0。',[p+'BhattScholze/Perfectoidization/Interface/TheoryInterface.lean',p+'BhattScholze/Perfectoidization/Interface/CAlg/Comparison.lean',p+'BhattScholze/Perfectoidization/Interface/CAlg/Definition.lean',p+'BhattScholze/Perfectoidization/Interface/CAlg/DerivedCorollary.lean'])
add(11,'IntegralExistenceを一般の初期極限・指定単位のbridge・残る存在に分割。',[p+'InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/InitialValueCone.lean',p+'BhattScholze/Perfectoidization/Interface/InitialBridge.lean',p+'BhattScholze/Perfectoidization/Interface/IntegralExistence.lean'])
assert not (R/'SerrePositivity/Inputs/Perfectoidization.lean').exists()
f=(R/'SerrePositivity/BhattScholze/Perfectoidization/Finite.lean').read_text();assert 'Algebra.FinitePresentation' in f
add(12,'旧Inputs wrapper削除。FiniteはBS版を直接呼び、FinitePresentationを含む元の型の引数列を明示して保存。',[p+'BhattScholze/Perfectoidization/Finite.lean'],{'strict_comparison':'actual-preservation/009/assessment.json','signature_restoration':'finite-fp-restoration.json'})
add(13,'TensorCompatibilityをBS集約へ追加して公開。',[p+'BhattScholze/Perfectoidization/TensorCompatibility.lean'],{'root_reachability':pub})
add(14,'DerivedからInterface、RootAdjunctionはConstruction、FiniteProductはPrism/Perfectoid。drafts将来欄18本は第一行だけ。',[p+'BhattScholze/Perfectoidization/Construction/RootAdjunction.lean',p+'BhattScholze/Prism/Perfectoid/FiniteProduct.lean'],{'draft_headers':'draft-header-plan.json'})
add(15,'R8-9の工程・旧・古い利用先をコメントだけ訂正。',[],{'comment_receipt':'bundle-docs-receipt.json'})
renames=[r for r in owners if r['old'].split('.')[-1]!=r['new'].split('.')[-1]];assert {r['new'].split('.')[-1] for r in renames}=={'perfectoidKernel_radical','IsAlmostZeroComplex'}
add(16,'BR43の二つの紛らわしい名前を改名。加群と複体の二つの系は別々に維持。',[],{'leaf_renames':renames})
add(17,'SupportedQuotientをExcisionTorの隣へ。',[p+'BhattScholze/Perfectoidization/SupportedQuotient.lean'])
add(18,'被約環の冪による零化補題をCommutativeAlgebraへ。',[p+'CommutativeAlgebra/Reduced/PowerAnnihilator.lean'])
f=(R/(p+'BhattScholze/Perfectoidization/CompletedTensor.lean')).read_text();assert '§10' in f
add(19,'CompletedTensorに§8と§10で共有する芯を明記、型・証明を変える分割をしない。',[p+'BhattScholze/Perfectoidization/CompletedTensor.lean'])
add(20,'IntegralClosureCompletionはAlmost、純粋なIntegralApproximationはCAへ。E3依存の存在はInterfaceに維持。',[p+'BhattScholze/Almost/IntegralClosureCompletion.lean',p+'CommutativeAlgebra/IntegralApproximation/FilteredAlgebra.lean'])
add(21,'Almostの古い説明・ノートと工程の記述を整理。属性文字列は維持。',[],{'comment_receipt':'bundle-docs-receipt.json'})
add(22,'B3維持表を照合：IntegralExistenceは分割後移動。PD固有cochainHomotopy・R83/Spectrum・広いR21・未使用削除は範囲外のまま。BS逆辺34は1解消33維持。',[],{'retentions':'../bulk-w1-b3/retained-and-deferred.json','edge_ledger':'actual-bs-reverse-edge-ledger.json','preexisting_section_edges':'actual-layer-comparison.json'})
rows=[{**r,**evidence[i+1],'stage0_plan':r['plan'],'status':'already-main' if r['status']=='already-main' else 'applied-awaiting-final-gates'} for i,r in enumerate(old['items'])];assert len(rows)==22
result={'baseline':old['baseline'],'applied_or_already_main':22,'final_complete':2,'total':22,'additional':0,'count_policy':'Applied does not mean complete until actual v3b/citations/root/all formal audits/full verify and full scope check all pass.','items':rows};(W/'scope-items-applied.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('22 scope rows mechanically reconciled; final gate pending')
