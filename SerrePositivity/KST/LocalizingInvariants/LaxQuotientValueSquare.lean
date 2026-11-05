module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientLegComparison
public import SerrePositivity.InfinityCategories.Core.CommutativeSquareRealization

/-!
概要：一般商の二脚の可換比較を、元の四つの BF 射を四辺に持つ実 Sp 正方形にする。
方針：全関手同型から得た h Sp の可換性を、四辺固定の単体的な正方形へ実現する。
規約：引き戻し性はここでは主張しない。使われ方：d8 の実 cospan 錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientSquare
local instance squareSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def cSource : value Φ A ⟶ value Φ C := valueMap Φ i ≫ valueMap Φ (laxFst p q)
def dSource : value Φ A ⟶ value Φ D := valueMap Φ i ≫ valueMap Φ (laxSnd p q)

include h in
lemma exists_square : ∃ s : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u},
    squareBottomEdge ≫ s = SSet.yonedaEquiv.symm (coherentNerveEdge (cSource Φ p q i)).edge ∧
    squareTopEdge ≫ s = SSet.yonedaEquiv.symm
      (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r))).edge ∧
    squareLeftEdge ≫ s = SSet.yonedaEquiv.symm (coherentNerveEdge (dSource Φ p q i)).edge ∧
    squareRightEdge ≫ s = SSet.yonedaEquiv.symm
      (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r))).edge := by
  exact exists_stableSquare_of_homMk_comm (X := Sp.{u})
    (coherentNerveEdge (cSource Φ p q i)).toTruncated
    (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r))).toTruncated
    (coherentNerveEdge (dSource Φ p q i)).toTruncated
    (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r))).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.valueMap_laxQuotientLegs_comm p q i r h Φ)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  Classical.choose (exists_square Φ p q i r h)

lemma square_bottom : squareBottomEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (cSource Φ p q i)).edge :=
  (Classical.choose_spec (exists_square Φ p q i r h)).1

lemma square_top : squareTopEdge ≫ square Φ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r))).edge :=
  (Classical.choose_spec (exists_square Φ p q i r h)).2.1

lemma square_left : squareLeftEdge ≫ square Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (dSource Φ p q i)).edge :=
  (Classical.choose_spec (exists_square Φ p q i r h)).2.2.1

lemma square_right : squareRightEdge ≫ square Φ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r))).edge :=
  (Classical.choose_spec (exists_square Φ p q i r h)).2.2.2

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientSquare
