module

public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientCospanInput

/-!
概要：一般商の抽象 Verdier 列の値は、元の二脚の実 pullback 正方形を与える。
方針：積・対角の指定極限錐から長方形の厳密延長・貼り合わせ・境界変形を順に適用する。
規約：元の E(A) と包含の両射影・商の二脚を保持。使われ方：Land–Tamme の抽象切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
local instance pullbackSquareSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  BinaryProductCospanNormalized.square (cSource (Φ := Φ) p q i) (dSource (Φ := Φ) p q i)
    (cLeg (Φ := Φ) p q r) (dLeg (Φ := Φ) p q r) (legs_comm p q i r h)
    (productSquare hΦ p q i r h) (productSquare_isPullback hΦ p q i r h)
    (productSquare_top hΦ p q i r h) (productSquare_right hΦ p q i r h)
    (productSquare_left hΦ p q i r h)

lemma square_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (square hΦ p q i r h) :=
  BinaryProductCospanNormalized.square_isPullback _ _ _ _ _ _ _ _ _ _

lemma square_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square hΦ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (cSource (Φ := Φ) p q i)).edge :=
  BinaryProductCospanNormalized.square_bottom _ _ _ _ _ _ _ _ _ _

lemma square_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square hΦ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dLeg (Φ := Φ) p q r)).edge :=
  BinaryProductCospanNormalized.square_top _ _ _ _ _ _ _ _ _ _

lemma square_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square hΦ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dSource (Φ := Φ) p q i)).edge :=
  BinaryProductCospanNormalized.square_left _ _ _ _ _ _ _ _ _ _

lemma square_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square hΦ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (cLeg (Φ := Φ) p q r)).edge :=
  BinaryProductCospanNormalized.square_right _ _ _ _ _ _ _ _ _ _

lemma square_vertex00 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (square hΦ p q i r h) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A) :=
  NativeSquareRows.vertex00 _ _ (square_bottom hΦ p q i r h)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (square hΦ p q i r h)

def cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (cospan hΦ p q i r h) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (square hΦ p q i r h)

lemma cone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (cone hΦ p q i r h) := square_isPullback hΦ p q i r h

lemma cone_vertex : (cone hΦ p q i r h).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A) := by
  have hv := FiberModel.coneSquare_apex (cone hΦ p q i r h)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone hΦ p q i r h) = square hΦ p q i r h := by
    simp only [cone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare, Iso.inv_hom_id_assoc]
  rw [hs] at hv
  exact hv.symm.trans (square_vertex00 hΦ p q i r h)

lemma cospan_C : horn₂₂.ι₀₂ ≫ cospan hΦ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (cLeg (Φ := Φ) p q r)).edge := by
  rw [cospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, square_right]

lemma cospan_D : horn₂₂.ι₁₂ ≫ cospan hΦ p q i r h =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dLeg (Φ := Φ) p q r)).edge := by
  rw [cospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, square_top]

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
