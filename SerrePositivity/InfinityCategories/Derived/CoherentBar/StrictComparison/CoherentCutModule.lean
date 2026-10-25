module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutTheta
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanModuleMap

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarCutModule (n : ℕ) : RightModule R D :=
  moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
    (dgCoherentBarCutTheta R D G n) (dgCoherentBarCutTheta_maurerCartan R D G n)

def dgCoherentBarCutModuleInclusion (n : ℕ) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G n) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) :=
  dgBarMaurerCartanModuleMap R D (dgCoherentBarCutTheta R D G n)
    (dgCoherentBarNormalizedTheta R D G) (dgCoherentBarCutTheta_maurerCartan R D G n)
    (dgCoherentBarNormalizedTheta_maurerCartan R D G (dgCoherentBarMaurerCartan_unconditional R D G))
    (dgCoherentBarCutInclusion R D G n) (dgCoherentBarCutTheta_inclusion R D G n)

@[simp]
lemma dgCoherentBarCutModuleInclusion_eval_f (n : ℕ) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgCoherentBarCutModuleInclusion R D G n)).f q =
      ((moduleEvaluation R D x).map (dgCoherentBarCutInclusion R D G n)).f q :=
  dgBarMaurerCartanModuleMap_eval_f R D _ _ _ _ _ _ x q

lemma dgCoherentBarCutModuleInclusion_injective (n : ℕ) (x : D) (q : ℤ) :
    Function.Injective (((moduleEvaluation R D x).map (dgCoherentBarCutModuleInclusion R D G n)).f q) := by
  rw [dgCoherentBarCutModuleInclusion_eval_f]
  have hr : ((moduleEvaluation R D x).map (dgCoherentBarCutInclusion R D G n)).f q ≫
      ((moduleEvaluation R D x).map (dgCoherentBarCutProjection R D G n)).f q = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
      dgCoherentBarCutInclusion_projection, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f]
  have hret : Function.LeftInverse
      (((moduleEvaluation R D x).map (dgCoherentBarCutProjection R D G n)).f q)
      (((moduleEvaluation R D x).map (dgCoherentBarCutInclusion R D G n)).f q) := by
    intro z
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using!
      ConcreteCategory.congr_hom hr z
  exact hret.injective

end SerrePositivity.InfinityCategories
