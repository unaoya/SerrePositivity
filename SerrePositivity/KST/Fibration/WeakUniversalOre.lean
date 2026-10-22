module
public import SerrePositivity.KST.Fibration.WeakEquivalences
public import SerrePositivity.KST.LocalizingInvariants.StableCospanPullbacks
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection

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
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj)
    (hR : IsPullbackSquare R) :
    (squareBottomArrow R).edge ∈ weakEquivalences i ↔
      (squareTopArrow R).edge ∈ weakEquivalences i :=
  weakEquivalences_pullback_iff h ((β_ Δ[1] Δ[1]).hom ≫ R)
    ((isPullbackSquare_iff_transpose R).mp hR)

/-- 任意の辺と指定した W 辺は、両入力を保つ普遍 Ore pullback に補完できる。 -/
theorem weakEquivalences_rightOre_pullback
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {x y z : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) x z)
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y z)
    (hs : s.edge ∈ weakEquivalences i) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj,
      IsPullbackSquare R ∧ squareRightEdge ≫ R = yonedaEquiv.symm f.edge ∧
        squareTopEdge ≫ R = yonedaEquiv.symm s.edge ∧
        (squareBottomArrow R).edge ∈ weakEquivalences i := by
  obtain ⟨R, hR, hr, ht⟩ := exists_stable_pullbackSquare_of_edges f s
  refine ⟨R, hR, hr, ht, (weakEquivalences_pullback_bottom_top h R hR).mpr ?_⟩
  have he : (squareTopArrow R).edge = s.edge :=
    (squareTopArrow_edge R).trans
      ((congrArg yonedaEquiv ht).trans (yonedaEquiv.apply_symm_apply s.edge))
  exact he.symm ▸ hs

end SerrePositivity.KST.Fibration
