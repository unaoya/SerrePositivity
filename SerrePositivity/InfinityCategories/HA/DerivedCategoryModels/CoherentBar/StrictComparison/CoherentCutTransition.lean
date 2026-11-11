module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutModule
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanInclusionComparison

/-!
概要：単体次元の上限を増やす元の実 dg 加群射を構成する。
方針：内部射の包含可換式から θ の可換式を導き、MC 微分変更後の射へ戻す。
規約：全次数成分は同じ部分族直和の包含である。
使われ方：実段階の列と全 bar への余錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarCutGradedMap {n m : ℕ} (_h : n ≤ m) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G n ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G m :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G m

@[reassoc]
lemma dgCoherentBarCutGradedMap_inclusion {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarCutGradedMap R D G h ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G m =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n := by
  apply Sigma.hom_ext
  intro s
  dsimp only [dgCoherentBarCutGradedMap]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι_assoc,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection_ι_assoc R D G m ⟨s.val, s.property.trans h⟩,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_ι]

lemma dgCoherentBarCutGradedMap_theta {n m : ℕ} (h : n ≤ m) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgCoherentBarCutGradedMap R D G h)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G m)).f 1 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta R D G m) =
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G n)
      (dgCoherentBarCutGradedMap R D G h)).f 1 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta R D G n) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarModuleTheta_comparison_of_inclusions R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G m)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G m) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_projection R D G m)
    (dgCoherentBarCutGradedMap R D G h) (dgCoherentBarCutGradedMap_inclusion R D G h)
    _ _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_inclusion R D G n) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_inclusion R D G m)

def dgCoherentBarCutModuleMap {n m : ℕ} (h : n ≤ m) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G n) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G m) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanModuleMap R D _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_maurerCartan R D G n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_maurerCartan R D G m) (dgCoherentBarCutGradedMap R D G h)
    (dgCoherentBarCutGradedMap_theta R D G h)

@[simp]
lemma dgCoherentBarCutModuleMap_eval_f {n m : ℕ} (h : n ≤ m) (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarCutModuleMap R D G h)).f q =
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarCutGradedMap R D G h)).f q :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanModuleMap_eval_f R D _ _ _ _ _ _ x q

@[reassoc]
lemma dgCoherentBarCutModuleMap_inclusion {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarCutModuleMap R D G h ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion R D G m =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion R D G n := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgCoherentBarCutModuleMap_eval_f, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion_eval_f]
  rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
    dgCoherentBarCutGradedMap_inclusion]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
