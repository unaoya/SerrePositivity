module

public import SerrePositivity.KST.LocalizingInvariants.StableCospanPullbacks
public import SerrePositivity.KST.LocalizingInvariants.TammeDenominatorClosure
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection

/-!
概要：指定した Tamme 分母と任意の辺の cospan を、実普遍 Ore pullback へ補完する。
方針：任意 cospan の普遍 pullback と、元の反転集合の基底変更による閉性を使う。
規約：同じ二入力辺を厳密に保ち、正方形の普遍性も実証する。
使われ方：局所化後の写像空間の相対分数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

lemma tammeLocalizingEdges_pullback_bottom_top
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj) (hR : IsPullbackSquare R) :
    (squareBottomArrow R).edge ∈ tammeLocalizingEdges p q ↔
      (squareTopArrow R).edge ∈ tammeLocalizingEdges p q := by
  have h := tammeLocalizingEdges_pullback_iff p q ((β_ Δ[1] Δ[1]).hom ≫ R)
    ((isPullbackSquare_iff_transpose R).mp hR)
  exact h

lemma tammeLocalizingEdges_rightOre_pullback {x y z : (laxCategory p q).obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) x z)
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y z)
    (hs : s.edge ∈ tammeLocalizingEdges p q) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj,
      IsPullbackSquare R ∧ squareRightEdge ≫ R = SSet.yonedaEquiv.symm f.edge ∧
        squareTopEdge ≫ R = SSet.yonedaEquiv.symm s.edge ∧
        (squareBottomArrow R).edge ∈ tammeLocalizingEdges p q := by
  obtain ⟨R, hR, hr, ht⟩ := exists_stable_pullbackSquare_of_edges f s
  refine ⟨R, hR, hr, ht, (tammeLocalizingEdges_pullback_bottom_top p q R hR).mpr ?_⟩
  have he : (squareTopArrow R).edge = s.edge :=
    (squareTopArrow_edge R).trans
      ((congrArg SSet.yonedaEquiv ht).trans (SSet.yonedaEquiv.apply_symm_apply s.edge))
  exact he.symm ▸ hs

end SerrePositivity.KST.LocalizingInvariants
