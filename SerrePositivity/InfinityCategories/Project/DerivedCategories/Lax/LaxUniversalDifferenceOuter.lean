module


public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceRectangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierInvariantFiber

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def outerSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (rectangle p q i r h).diagram 1

lemma outerSquare_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow i).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_leftEdge,
    (rectangle p q i r h).left_eq, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_bottom]

lemma outerSquare_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow r).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge,
    (rectangle p q i r h).top_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.quotientCompositionTriangle p q r).d₁]

lemma outerSquare_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge,
    (rectangle p q i r h).bottom_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm, (zeroCompositionTriangle p q i r).d₁]

def outerDiagram : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u} := by
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare p q i r h
  have ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex S 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A := by
    have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source S
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare_bottom, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow i).src_eq] at ht
    exact ht.symm
  have hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex S 1 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (laxCategory p q) := by
    have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target S
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare_bottom, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow i).tgt_eq] at ht
    exact ht.symm
  have hq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex S 1 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex Q := by
    have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target S
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare_right, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow r).tgt_eq] at ht
    exact ht.symm
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex S 0 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := by
    have ht := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target S
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare_left, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A)).tgt_eq] at ht
    exact ht.symm
  exact {
    toVerdierSequence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h
    square := S
    left_eq := ha
    middle_eq := hp
    right_eq := hq
    bottom_edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare_bottom p q i r h
    right_edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare_right p q i r h
    zero_corner := by rw [hz, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]; exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
