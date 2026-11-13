module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductComponentValues

/-! # 元の全比較正方形の四辺と同じ完全関手の値
概要：指定比較道を持つ同じ Cat^perf 正方形の四辺を、元の完全関手として回収する。
方針：全部分複体の単射で元の辺の等式を反映し、同じ不変量で像を取る。
規約：四辺をホモトピー類の別代表へ選び直さない。使われ方：実積正方形の辺の計算。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 同じ Cat^perf 比較正方形の bottom 辺は、元の完全関手の同じ辺。 -/
lemma universalSquare_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.universalSquare =
    SSet.yonedaEquiv.symm (perfectStableArrow d.inclusion
      d.left_complete d.middle_complete).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s) d.universalSquare_inclusion).trans
      (d.universalRawSquare_edges.1.trans
        (perfectStableArrow_inclusion d.inclusion
          d.left_complete d.middle_complete).symm))

/-- 同じ Cat^perf 比較正方形の top 辺は、元の完全関手の同じ辺。 -/
lemma universalSquare_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ d.universalSquare =
    SSet.yonedaEquiv.symm (perfectStableArrow (IdentityLax.exactDiagonal d.sequence.right)
      d.sequence.right_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right)
        (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ s) d.universalSquare_inclusion).trans
      (d.universalRawSquare_edges.2.1.trans
        (perfectStableArrow_inclusion (IdentityLax.exactDiagonal d.sequence.right)
          d.sequence.right_complete (perfectLaxCategory_isIdempotentComplete (𝟙
            d.sequence.right) (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)).symm))

/-- 同じ Cat^perf 比較正方形の left 辺は、元の完全関手の同じ辺。 -/
lemma universalSquare_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ d.universalSquare =
    SSet.yonedaEquiv.symm (perfectStableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion
      d.sequence.projection)
      d.left_complete d.sequence.right_complete).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s) d.universalSquare_inclusion).trans
      (d.universalRawSquare_edges.2.2.1.trans
        (perfectStableArrow_inclusion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion
          d.sequence.projection)
          d.left_complete d.sequence.right_complete).symm))

/-- 同じ Cat^perf 比較正方形の right 辺は、元の完全関手の同じ辺。 -/
lemma universalSquare_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.universalSquare =
    SSet.yonedaEquiv.symm (perfectStableArrow (LaxUniversalDifference.exactLift p q
      d.sequence.projection)
      d.middle_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙
        d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s) d.universalSquare_inclusion).trans
      (d.universalRawSquare_edges.2.2.2.trans
        (perfectStableArrow_inclusion (LaxUniversalDifference.exactLift p q d.sequence.projection)
          d.middle_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙
            d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)).symm))

variable (F : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 同じ Sp 比較正方形の bottom 辺は、元の完全関手の同じ値の射の類。 -/
lemma universalValueSquare_bottom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (d.universalValueSquare F)) =
      Arrow.mk (perfectInvariantHoArrow F d.inclusion
        d.left_complete d.middle_complete) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (d.universalSquare ≫ F)) = _
  rw [← Category.assoc, d.universalSquare_bottom,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

/-- 同じ Sp 比較正方形の top 辺は、元の完全関手の同じ値の射の類。 -/
lemma universalValueSquare_top_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop (d.universalValueSquare F)) =
      Arrow.mk (perfectInvariantHoArrow F (IdentityLax.exactDiagonal d.sequence.right)
        d.sequence.right_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right)
          (𝟙 d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (d.universalSquare ≫ F)) = _
  rw [← Category.assoc, d.universalSquare_top,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

/-- 同じ Sp 比較正方形の left 辺は、元の完全関手の同じ値の射の類。 -/
lemma universalValueSquare_left_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoLeft (d.universalValueSquare F)) =
      Arrow.mk (perfectInvariantHoArrow F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion
        d.sequence.projection)
        d.left_complete d.sequence.right_complete) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (d.universalSquare ≫ F)) = _
  rw [← Category.assoc, d.universalSquare_left,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

/-- 同じ Sp 比較正方形の right 辺は、元の完全関手の同じ値の射の類。 -/
lemma universalValueSquare_right_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (d.universalValueSquare F)) =
      Arrow.mk (perfectInvariantHoArrow F (LaxUniversalDifference.exactLift p q
        d.sequence.projection)
        d.middle_complete (perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙
          d.sequence.right)
        d.sequence.right_complete d.sequence.right_complete)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (d.universalSquare ≫ F)) = _
  rw [← Category.assoc, d.universalSquare_right,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
