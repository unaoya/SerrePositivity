module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceRectangle
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierInvariantFiber

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
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def outerSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ pastingSquare (rectangle p q i r h).diagram 1

lemma outerSquare_bottom : squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_bottom, pastingSquare_outer_leftEdge,
    (rectangle p q i r h).left_eq, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_left, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_bottom]

lemma outerSquare_right : squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow r).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_right, pastingSquare_topEdge,
    (rectangle p q i r h).top_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm, (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.quotientCompositionTriangle p q r).d₁]

lemma outerSquare_left : squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory A)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_left, pastingSquare_bottomEdge,
    (rectangle p q i r h).bottom_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm, (zeroCompositionTriangle p q i r).d₁]

def outerDiagram : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u} := by
  let S := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare p q i r h
  have ha : squareVertex S 0 0 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex A := by
    have ht := squareBottomEdge_source S
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_bottom, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i).src_eq] at ht
    exact ht.symm
  have hp : squareVertex S 1 0 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex (laxCategory p q) := by
    have ht := squareBottomEdge_target S
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_bottom, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i).tgt_eq] at ht
    exact ht.symm
  have hq : squareVertex S 1 1 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex Q := by
    have ht := squareRightEdge_target S
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_right, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow r).tgt_eq] at ht
    exact ht.symm
  have hz : squareVertex S 0 1 = _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory.{u} := by
    have ht := squareLeftEdge_target S
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_left, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.toZeroCategory A)).tgt_eq] at ht
    exact ht.symm
  exact {
    toVerdierSequence := _root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h
    square := S
    left_eq := ha
    middle_eq := hp
    right_eq := hq
    bottom_edge := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_bottom p q i r h
    right_edge := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_right p q i r h
    zero_corner := by rw [hz, _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject_vertex]; exact _root_.SerrePositivity.InfinityCategories.Stable.Exact.zeroCategory_isZero }

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerSquare := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerSquare_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerSquare_left := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerSquare_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerDiagram._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerSquare._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.outerSquare.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare.eq_1
