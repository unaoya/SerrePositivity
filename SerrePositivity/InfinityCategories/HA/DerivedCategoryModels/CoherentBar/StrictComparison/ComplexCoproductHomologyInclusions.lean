module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCoproductHomologyLegs

/-!
概要：直和ホモロジー同型が実 summand 包含を標準包含へ送ること。
方針：実直和と colim 模型の比較、短複体ホモロジーの自然性を合わせる。
規約：全整数次数の実包含を使う。
使われ方：実 coherent bar の層ホモロジー上の微分係数の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {I : Type u} (K : I → Complex R)

@[reassoc]
lemma dgComplexCoproductHomologyIso_ι (i : I) (q : ℤ) :
    HomologicalComplex.homologyMap (Sigma.ι K i) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso R K q).hom = Sigma.ι (fun j => (K j).homology q) i := by
  let A := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductColimitIso R K
  let B := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductColimitHomologyIso R K q
  let E := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyDiagramIso R K q
  let P := (coproductIsCoproduct (fun j => (K j).homology q)).coconePointUniqueUpToIso
    (colimit.isColimit (Discrete.functor (fun j => (K j).homology q)))
  have hleg : Sigma.ι K i ≫ A.inv = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoproductComplexLeg R K i := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoproductComplexLeg_comparison R K i]
    simp only [A, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hφ : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso R K q).hom =
      HomologicalComplex.homologyMap A.inv q ≫ B.hom ≫ (colim.mapIso E).inv ≫ P.inv := by
    simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductColimitHomologyIso,
      A, B, E, P, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_inv,
      Category.assoc]
  rw [hφ, ← Category.assoc (HomologicalComplex.homologyMap (Sigma.ι K i) q)
    (HomologicalComplex.homologyMap A.inv q), ← HomologicalComplex.homologyMap_comp, hleg,
    ← Category.assoc _ B.hom]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductColimitHomologyIso_leg R K i q, Category.assoc]
  change E.hom.app ⟨i⟩ ≫ _ ≫ colim.map E.inv ≫ P.inv = _
  rw [colimit.ι_map_assoc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact (coproductIsCoproduct (fun j => (K j).homology q)).comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit (Discrete.functor (fun j => (K j).homology q))) (Discrete.mk i)

@[reassoc]
lemma dgComplexCoproductHomologyIso_ι_inv (i : I) (q : ℤ) :
    Sigma.ι (fun j => (K j).homology q) i ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso R K q).inv =
      HomologicalComplex.homologyMap (Sigma.ι K i) q := by
  rw [← dgComplexCoproductHomologyIso_ι R K i q, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma dgComplexCoproductHomologyIso_desc {N : Complex R} (f : ∐ K ⟶ N) (q : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso R K q).inv ≫ HomologicalComplex.homologyMap f q =
      Sigma.desc (fun i => HomologicalComplex.homologyMap (Sigma.ι K i ≫ f) q) := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, dgComplexCoproductHomologyIso_ι_inv,
    ← HomologicalComplex.homologyMap_comp, Sigma.ι_comp_desc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
