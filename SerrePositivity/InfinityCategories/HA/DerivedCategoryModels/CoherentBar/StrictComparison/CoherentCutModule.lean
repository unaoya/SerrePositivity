module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutTheta
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanModuleMap

/-!
概要：単体次元上限を持つ実正規化 bar の dg 加群段階と元の bar への実包含。
方針：制限 θ の MC 方程式で内部直和の微分を変更し、同じ全次数の包含を戻す。
規約：元の全 dg 作用と高次 HA 成分を保つ。
使われ方：h-projective な次元層による帰納と telescope。
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

def dgCoherentBarCutModule (n : ℕ) : RightModule R D :=
  moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G n))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta R D G n) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_maurerCartan R D G n)

def dgCoherentBarCutModuleInclusion (n : ℕ) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgCoherentBarCutModule R D G n) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanModuleMap R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta R D G n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_maurerCartan R D G n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta_maurerCartan R D G (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta_inclusion R D G n)

@[simp]
lemma dgCoherentBarCutModuleInclusion_eval_f (n : ℕ) (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarCutModuleInclusion R D G n)).f q =
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n)).f q :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanModuleMap_eval_f R D _ _ _ _ _ _ x q

lemma dgCoherentBarCutModuleInclusion_injective (n : ℕ) (x : D) (q : ℤ) :
    Function.Injective (((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarCutModuleInclusion R D G n)).f q) := by
  rw [dgCoherentBarCutModuleInclusion_eval_f]
  have hr : ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n)).f q ≫
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G n)).f q = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_projection, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f]
  have hret : Function.LeftInverse
      (((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G n)).f q)
      (((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G n)).f q) := by
    intro z
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using!
      ConcreteCategory.congr_hom hr z
  exact hret.injective

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
