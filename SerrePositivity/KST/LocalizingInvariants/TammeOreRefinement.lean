module

public import SerrePositivity.KST.LocalizingInvariants.TammeFiniteDenominators
public import SerrePositivity.InfinityCategories.Stable.CommutativeSquareRealization

/-!
概要：元の分母と任意の辺の cospan を、元の四辺を保つ実 Ore 正方形へ細分する。
方針：安定閉包の右分数計算を実辺に戻し、可換式を実二単体二枚で実現する。
規約：正方形の普遍 pullback 性や全次元の相対充填はまだ主張しない。
使われ方：元の商への矢印・有限図式の分数表示。
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
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma tammeLocalizingEdges_rightOre {x y z : (laxCategory p q).obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) x z)
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y z)
    (hs : s.edge ∈ tammeLocalizingEdges p q) :
    ∃ (a : (laxCategory p q).obj _⦋0⦌)
      (t : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a x)
      (g : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a y),
      t.edge ∈ tammeLocalizingEdges p q ∧
      SSet.Truncated.HomotopyCategory.homMk t ≫ SSet.Truncated.HomotopyCategory.homMk f =
        SSet.Truncated.HomotopyCategory.homMk g ≫ SSet.Truncated.HomotopyCategory.homMk s := by
  let P := essentialImage (pullbackInclusion p q)
  let φ : (stableHoClosure P).trW.LeftFraction
      (HomotopyCategory.mk x) (HomotopyCategory.mk y) :=
    ⟨SSet.Truncated.HomotopyCategory.homMk f, SSet.Truncated.HomotopyCategory.homMk s,
      (tammeLocalizingEdges_iff_trW p q s).mp hs⟩
  obtain ⟨ψ, h⟩ := φ.exists_rightFraction
  rcases ψ with @⟨a, t, ht, g⟩
  obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨t, rfl⟩ := homotopyCategory_homMk_surjective a x t
  obtain ⟨g, rfl⟩ := homotopyCategory_homMk_surjective a y g
  exact ⟨a, t, g, (tammeLocalizingEdges_iff_trW p q t).mpr ht, h⟩

/-- 元の入力二辺を上辺・右辺として保持する実正方形と、新しい実分母。 -/
lemma tammeLocalizingEdges_rightOre_square {x y z : (laxCategory p q).obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) x z)
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y z)
    (hs : s.edge ∈ tammeLocalizingEdges p q) :
    ∃ (a : (laxCategory p q).obj _⦋0⦌)
      (t : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a x)
      (g : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a y),
      t.edge ∈ tammeLocalizingEdges p q ∧
      ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj,
        squareBottomEdge ≫ R = SSet.yonedaEquiv.symm t.edge ∧
        squareTopEdge ≫ R = SSet.yonedaEquiv.symm s.edge ∧
        squareLeftEdge ≫ R = SSet.yonedaEquiv.symm g.edge ∧
        squareRightEdge ≫ R = SSet.yonedaEquiv.symm f.edge := by
  obtain ⟨a, t, g, ht, h⟩ := tammeLocalizingEdges_rightOre p q f s hs
  obtain ⟨R, hb, hu, hl, hr⟩ := exists_stableSquare_of_homMk_comm t s g f h
  exact ⟨a, t, g, ht, R, hb, hu, hl, hr⟩

end SerrePositivity.KST.LocalizingInvariants
