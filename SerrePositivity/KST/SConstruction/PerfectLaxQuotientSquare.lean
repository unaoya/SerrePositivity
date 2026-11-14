module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

/-! # 元の二脚を持つ Cat^perf の実正方形
概要：未完備な実商と完備化の入力から、元の四辺を固定した coherent 四角形を作る。
方針：Cat^perf の可換な射の類を、同じ四辺を持つ二三角形として貼り合わせる。
規約：引き戻し性は後続。使われ方：Cat^perf の不変量による LT の四角形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 元の四つの完全関手の辺を保つ、実 Cat^perf 四角形が存在する。 -/
lemma exists_square : ∃ s : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u},
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s =
        SSet.yonedaEquiv.symm (perfectStableArrow d.cSource d.left_complete d.c_complete).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ s =
        SSet.yonedaEquiv.symm (perfectStableArrow d.dLeg d.d_complete d.right_complete).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s =
        SSet.yonedaEquiv.symm (perfectStableArrow d.dSource d.left_complete d.d_complete).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s =
        SSet.yonedaEquiv.symm (perfectStableArrow d.cLeg d.c_complete d.right_complete).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm
    (perfectStableArrow d.cSource d.left_complete d.c_complete).toTruncated
    (perfectStableArrow d.dLeg d.d_complete d.right_complete).toTruncated
    (perfectStableArrow d.dSource d.left_complete d.d_complete).toTruncated
    (perfectStableArrow d.cLeg d.c_complete d.right_complete).toTruncated d.legs_comm

/-- 同じ四辺を持つ実 Cat^perf 四角形。 -/
def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u} :=
  Classical.choose d.exists_square

/-- 同じ四角形の下辺は元の C 側の射影。 -/
lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.square =
    SSet.yonedaEquiv.symm (perfectStableArrow d.cSource d.left_complete d.c_complete).edge :=
  (Classical.choose_spec d.exists_square).1

/-- 同じ四角形の上辺は元の D 側の商の脚と完備化。 -/
lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ d.square =
    SSet.yonedaEquiv.symm (perfectStableArrow d.dLeg d.d_complete d.right_complete).edge :=
  (Classical.choose_spec d.exists_square).2.1

/-- 同じ四角形の左辺は元の D 側の射影。 -/
lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ d.square =
    SSet.yonedaEquiv.symm (perfectStableArrow d.dSource d.left_complete d.d_complete).edge :=
  (Classical.choose_spec d.exists_square).2.2.1

/-- 同じ四角形の右辺は元の C 側の商の脚と完備化。 -/
lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.square =
    SSet.yonedaEquiv.symm (perfectStableArrow d.cLeg d.c_complete d.right_complete).edge :=
  (Classical.choose_spec d.exists_square).2.2.2

/-- 四角形全体を、同じ Cat^perf 上の Sp 値関手で写す。 -/
def valueSquare (F : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Spectra.Sp.{u} := d.square ≫ F

/-- 値の下辺は、元の C 側の射の同じ辺の像。 -/
lemma valueSquare_bottom (F : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.valueSquare F = SSet.yonedaEquiv.symm
      ((perfectStableArrow d.cSource d.left_complete d.c_complete).map F).edge := by
  rw [valueSquare, ← Category.assoc, d.square_bottom, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 値の上辺は、元の D 側の完備化後の脚の同じ辺の像。 -/
lemma valueSquare_top (F : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ d.valueSquare F = SSet.yonedaEquiv.symm
      ((perfectStableArrow d.dLeg d.d_complete d.right_complete).map F).edge := by
  rw [valueSquare, ← Category.assoc, d.square_top, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 値の左辺は、元の D 側の射の同じ辺の像。 -/
lemma valueSquare_left (F : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ d.valueSquare F = SSet.yonedaEquiv.symm
      ((perfectStableArrow d.dSource d.left_complete d.d_complete).map F).edge := by
  rw [valueSquare, ← Category.assoc, d.square_left, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 値の右辺は、元の C 側の完備化後の脚の同じ辺の像。 -/
lemma valueSquare_right (F : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.valueSquare F = SSet.yonedaEquiv.symm
      ((perfectStableArrow d.cLeg d.c_complete d.right_complete).map F).edge := by
  rw [valueSquare, ← Category.assoc, d.square_right, SSet.yonedaEquiv_symm_comp]
  rfl

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
