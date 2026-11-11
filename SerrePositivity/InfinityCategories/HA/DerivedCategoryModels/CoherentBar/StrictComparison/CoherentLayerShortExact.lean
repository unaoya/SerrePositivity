module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerRemainder
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：実正規化 coherent bar の隣接段階と次元層は短完全列をなす。
方針：次数ごとの単射・全射と、最高次元を除く残余の一段下降を合わせる。
規約：全高次 HA 成分を含む実微分を保持する。
使われ方：単体次元フィルトレーションの段階商と内部複体の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarStageMap_toLayer_zero (x : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1) = 0 := by
  ext q z
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_annihilate R D G x q (Nat.lt_succ_self n) z.val z.property

def dgCoherentBarLayerSequence (x : D) (n : ℕ) : ShortComplex (_root_.SerrePositivity.DifferentialGraded.Complex R) :=
  ShortComplex.mk (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) (dgCoherentBarStageMap_toLayer_zero R D G x n)

lemma dgCoherentBarLayerSequence_shortExact (x : D) (n : ℕ) :
    (dgCoherentBarLayerSequence R D G x n).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    change (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G (n + 1))
      z.val = 0 at hz
    have hm := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_kernel_mem R D G x q n z.val z.property hz
    exact ⟨⟨z.val, hm⟩, rfl⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (Submodule.inclusion
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_mono R D G x q (Nat.le_succ n)))
    exact Submodule.inclusion_injective _
  · exact (ModuleCat.epi_iff_surjective _).mpr (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer_surjective R D G x q (n + 1))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
