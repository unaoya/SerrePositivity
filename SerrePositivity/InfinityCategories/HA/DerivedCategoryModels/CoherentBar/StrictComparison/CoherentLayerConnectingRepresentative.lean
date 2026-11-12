module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerCycleBoundary

/-!
概要：実次元層の長完全列の連結射を、持上げた cycle の境界で表す。
方針：実部分複体の単射性と長完全列の代表元公式を適用する。
規約：内部微分・theta の全項を含む実境界である。
使われ方：一次ホモロジー微分の係数の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet

lemma dgComplex_liftCycles_iCycles (R : Type u) [CommRing R] (K : _root_.SerrePositivity.DifferentialGraded.Complex R) (q : ℤ) :
    K.liftCycles (K.iCycles q) (q + 1) (by apply ComplexShape.next_eq'; rfl)
      (K.iCycles_d q (q + 1)) = 𝟙 _ := by
  rw [← cancel_mono (K.iCycles q), HomologicalComplex.liftCycles_i, Category.id_comp]

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarLayerCycleBoundary_closed (x : D) (q : ℤ) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleBoundary R D G x q n ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).d (q + 1) (q + 2) = 0 := by
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n)
  letI : Mono (f.f (q + 2)) := (ModuleCat.mono_iff_injective _).mpr (by
    change Function.Injective (Submodule.inclusion
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_mono R D G x (q + 2) (Nat.le_succ n)))
    exact Submodule.inclusion_injective _)
  rw [← cancel_mono (f.f (q + 2)), Category.assoc, ← f.comm,
    ← Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleBoundary_stageMap R D G x q n]
  rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_comp]

lemma dgCoherentBarLayerConnecting_representative (x : D) (q : ℤ) (n : ℕ) :
    ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1))).homologyπ q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).δ q (q + 1) (by rfl) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).liftCycles
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleBoundary R D G x q n) (q + 2)
      (by apply ComplexShape.next_eq'; change (q + 1) + 1 = q + 2; omega)
      (dgCoherentBarLayerCycleBoundary_closed R D G x q n) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).homologyπ (q + 1) := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).δ_eq q (q + 1) (by rfl)
    (((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1))).iCycles q)
    (HomologicalComplex.iCycles_d _ _ _) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleLift R D G x q n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleLift_toLayer R D G x q n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleBoundary R D G x q n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerCycleBoundary_stageMap R D G x q n) (q + 2)
    (by apply ComplexShape.next_eq'; change (q + 1) + 1 = q + 2; omega)
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence, dgComplex_liftCycles_iCycles, Category.id_comp] using! h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
