module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.WeakEquivalences
public import SerrePositivity.KST.LocalizingInvariants.StableCospanPullbacks
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection

/-! # Verdier 列の元の W 辺による普遍 Ore 四角形 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の普遍 pullback の上辺と下辺の W 所属は同値。 -/
theorem weakEquivalences_pullback_bottom_top
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow R).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ↔
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pullback_iff h ((β_ Δ[1] Δ[1]).hom ≫ R)
    ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_transpose R).mp hR)

/-- 任意の辺と指定した W 辺は、両入力を保つ普遍 Ore pullback に補完できる。 -/
theorem weakEquivalences_rightOre_pullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {x y z : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) x z)
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y z)
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R = yonedaEquiv.symm f.edge ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R = yonedaEquiv.symm s.edge ∧
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow R).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  obtain ⟨R, hR, hr, ht⟩ := exists_stable_pullbackSquare_of_edges f s
  refine ⟨R, hR, hr, ht, (weakEquivalences_pullback_bottom_top h R hR).mpr ?_⟩
  have he : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R).edge = s.edge :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge R).trans
      ((congrArg yonedaEquiv ht).trans (yonedaEquiv.apply_symm_apply s.edge))
  exact he.symm ▸ hs

end SerrePositivity.KST.Fibration
