module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceRectangle
public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierInvariantFiber

/-!
概要：比較長方形の外周を、元の包含 i・商 r の実 Verdier 図式として読む。
方針：上下の指定合成三角形から外周の辺と零角を回収する。
規約：元の商を合成の同型な代用品に置き換えない。使われ方：局所化不変量の fiber 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def outerSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ pastingSquare (rectangle p q i r h).diagram 1

lemma outerSquare_bottom : squareBottomEdge ≫ outerSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow i).edge := by
  rw [outerSquare, square_transpose_bottom, pastingSquare_outer_leftEdge,
    (rectangle p q i r h).left_eq, square_transpose_left, comparisonSquare_bottom]

lemma outerSquare_right : squareRightEdge ≫ outerSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow r).edge := by
  rw [outerSquare, square_transpose_right, pastingSquare_topEdge,
    (rectangle p q i r h).top_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm, (quotientCompositionTriangle p q r).d₁]

lemma outerSquare_left : squareLeftEdge ≫ outerSquare p q i r h =
    SSet.yonedaEquiv.symm (stableArrow (toZeroCategory A)).edge := by
  rw [outerSquare, square_transpose_left, pastingSquare_bottomEdge,
    (rectangle p q i r h).bottom_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm, (zeroCompositionTriangle p q i r).d₁]

def outerDiagram : VerdierDiagram.{u} := by
  let S := outerSquare p q i r h
  have ha : squareVertex S 0 0 = stableVertex A := by
    have ht := squareBottomEdge_source S
    rw [outerSquare_bottom, Equiv.apply_symm_apply, (stableArrow i).src_eq] at ht
    exact ht.symm
  have hp : squareVertex S 1 0 = stableVertex (laxCategory p q) := by
    have ht := squareBottomEdge_target S
    rw [outerSquare_bottom, Equiv.apply_symm_apply, (stableArrow i).tgt_eq] at ht
    exact ht.symm
  have hq : squareVertex S 1 1 = stableVertex Q := by
    have ht := squareRightEdge_target S
    rw [outerSquare_right, Equiv.apply_symm_apply, (stableArrow r).tgt_eq] at ht
    exact ht.symm
  have hz : squareVertex S 0 1 = stableVertex zeroCategory.{u} := by
    have ht := squareLeftEdge_target S
    rw [outerSquare_left, Equiv.apply_symm_apply,
      (stableArrow (toZeroCategory A)).tgt_eq] at ht
    exact ht.symm
  exact {
    toVerdierSequence := laxQuotientVerdierSequence p q i r h
    square := S
    left_eq := ha
    middle_eq := hp
    right_eq := hq
    bottom_edge := outerSquare_bottom p q i r h
    right_edge := outerSquare_right p q i r h
    zero_corner := by rw [hz, stableObject_vertex]; exact zeroCategory_isZero }

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
