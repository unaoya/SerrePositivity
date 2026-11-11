module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyCoordinates

/-!
概要：直和ホモロジー同型と実 summand 包含の対応を準備する。
方針：関手圏の colim 模型への実包含と評価関手からの自然変換を使う。
規約：非有界複体の実直和を扱う。
使われ方：coherent bar のホモロジー係数射の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {I : Type u}

def dgCoproductEvaluationLeg (i : I) :
    (evaluation (Discrete I) (ModuleCat.{u} R)).obj ⟨i⟩ ⟶
      colim (J := Discrete I) (C := ModuleCat.{u} R) where
  app F := colimit.ι F ⟨i⟩
  naturality {F H} α := (colimit.ι_map α ⟨i⟩).symm

variable (K : I → Complex R)

def dgCoproductComplexLeg (i : I) : K i ⟶
    ((colim (J := Discrete I) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)) :=
  CochainComplex.ofHom (fun q => colimit.ι
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).X q) ⟨i⟩) (fun q =>
      colimit.ι_map ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).d q (q + 1)) ⟨i⟩)

lemma dgCoproductComplexLeg_comparison (i : I) :
    dgCoproductComplexLeg R K i ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductColimitIso R K).hom = Sigma.ι K i := by
  have h := (coproductIsCoproduct K).comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit (Discrete.functor K)) (Discrete.mk i)
  apply HomologicalComplex.Hom.ext
  funext q
  change colimit.ι ((Discrete.functor K) ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) q)
    ⟨i⟩ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso R (Discrete.functor K)).hom.f q ≫ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso_ι_assoc]
  exact congrArg (fun f => f.f q) h

def dgComplexCoproductColimitHomologyIso (q : ℤ) :
    (((colim (J := Discrete I) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K))).homology q ≅
    colimit (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).sc'
      (q - 1) q (q + 1)).homology) :=
  HomologicalComplex.homologyIsoSc' _ (q - 1) q (q + 1) (by simp) (by simp) ≪≫
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).sc'
      (q - 1) q (q + 1)).mapHomologyIso (colim (J := Discrete I) (C := ModuleCat.{u} R))

lemma dgComplexCoproductColimitHomologyIso_leg (i : I) (q : ℤ) :
    HomologicalComplex.homologyMap (dgCoproductComplexLeg R K i) q ≫
      (dgComplexCoproductColimitHomologyIso R K q).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyDiagramIso R K q).hom.app ⟨i⟩ ≫
      colimit.ι (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).sc'
        (q - 1) q (q + 1)).homology) ⟨i⟩ := by
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R (Discrete.functor K)).sc' (q - 1) q (q + 1)
  have heq : (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (.up ℤ)
      (q - 1) q (q + 1)).map (dgCoproductComplexLeg R K i) =
        S.mapNatTrans (dgCoproductEvaluationLeg R i) := by
    ext <;> rfl
  dsimp only [dgComplexCoproductColimitHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyIsoSc_naturality, Category.assoc, heq,
    ShortComplex.homologyMap_mapNatTrans]
  simp only [S, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
