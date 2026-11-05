module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductCone
public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientValueSquare
public import SerrePositivity.KST.LocalizingInvariants.BinaryProductCospanNormalized

/-!
概要：一般商の指定した積・対角 pullback を、元の二脚への変換の入力にする。
方針：既存の正方形を転置し、元の BF 積射・包含の組・対角を厳密に照合する。
規約：安定 Q と IsVerdierSequence は入力。使われ方：d8 の実二脚 pullback。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def cSource : value Φ A ⟶ value Φ C := LaxQuotientSquare.cSource Φ p q i
def dSource : value Φ A ⟶ value Φ D := LaxQuotientSquare.dSource Φ p q i
def cLeg : value Φ C ⟶ value Φ Q := valueMap Φ (laxQuotientCLeg p q r)
def dLeg : value Φ D ⟶ value Φ Q := valueMap Φ (laxQuotientDLeg p q r)

include h in
lemma legs_comm : SpectrumHo.hom (cSource (Φ := Φ) p q i) ≫
    SpectrumHo.hom (cLeg (Φ := Φ) p q r) =
      SpectrumHo.hom (dSource (Φ := Φ) p q i) ≫ SpectrumHo.hom (dLeg (Φ := Φ) p q r) :=
  valueMap_laxQuotientLegs_comm p q i r h Φ

def productSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ LaxUniversalProductNormalization.square hΦ p q i r h

lemma productSquare_isPullback : IsPullbackSquare (productSquare hΦ p q i r h) :=
  (isPullbackSquare_iff_transpose _).1
    (LaxUniversalProductNormalization.square_isPullback hΦ p q i r h)

lemma productSquare_top : squareTopEdge ≫ productSquare hΦ p q i r h =
    SSet.yonedaEquiv.symm
      (coherentNerveEdge (Binary.map (cLeg (Φ := Φ) p q r) (dLeg (Φ := Φ) p q r))).edge := by
  rw [productSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_top, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_right]
  rfl

lemma productSquare_right : squareRightEdge ≫ productSquare hΦ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (BinaryGraph.diagonal (value Φ Q))).edge := by
  rw [productSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_right, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_top]
  rfl

lemma productSquare_left : squareLeftEdge ≫ productSquare hΦ p q i r h =
    SSet.yonedaEquiv.symm
      (coherentNerveEdge (Binary.lift (cSource (Φ := Φ) p q i) (dSource (Φ := Φ) p q i))).edge := by
  rw [productSquare, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_left, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_bottom]
  rfl

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
