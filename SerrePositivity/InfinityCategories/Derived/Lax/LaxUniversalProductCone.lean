module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare

/-!
概要：元の BF 積射と対角の実 pullback 極限錐、その頂点は元の E(A)。
方針：境界変形で固定した四辺を回収し、保持した pullback 性を錐の極限性として公開する。
規約：二脚自身の cospan への変換は後続。使われ方：d8 の積・対角による実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

lemma square_bottom : squareBottomEdge ≫ square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge
      (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)).edge :=
  SquareFrame.square_bottom_of_boundary _ (square_boundary hΦ p q i r h)

lemma square_top : squareTopEdge ≫ square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q)))).edge :=
  SquareFrame.square_top_of_boundary _ (square_boundary hΦ p q i r h)

lemma square_left : squareLeftEdge ≫ square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (valueMap Φ (LaxUniversalDifference.kernelMap p q i r))).edge :=
  SquareFrame.square_left_of_boundary _ (square_boundary hΦ p q i r h)

lemma square_right : squareRightEdge ≫ square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r)).edge :=
  SquareFrame.square_right_of_boundary _ (square_boundary hΦ p q i r h)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} := pullbackCospan (square hΦ p q i r h)

def cone : JoinCone (cospan hΦ p q i r h) := pullbackCone (square hΦ p q i r h)

lemma cone_isLimit : IsLimitCone (cone hΦ p q i r h) := square_isPullback hΦ p q i r h

lemma cospan_product : horn₂₂.ι₀₂ ≫ cospan hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r)).edge := by
  rw [cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge, square_right]

lemma cospan_diagonal : horn₂₂.ι₁₂ ≫ cospan hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q)))).edge := by
  rw [cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge, square_top]

lemma square_source_vertex : squareVertex (square hΦ p q i r h) 0 0 =
    coherentNerveVertex (value Φ A) := by
  have he := squareBottomEdge_source (square hΦ p q i r h)
  rw [square_bottom] at he
  exact he.symm.trans ((congrArg (Sp.{u}.δ 1) (SSet.yonedaEquiv.apply_symm_apply
    (coherentNerveEdge
      (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)).edge)).trans
        (coherentNerveEdge
          (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)).src_eq)

lemma cone_vertex : (cone hΦ p q i r h).vertex = coherentNerveVertex (value Φ A) := by
  have he := FiberModel.coneSquare_apex (cone hΦ p q i r h)
  have hs : coneSquare (cone hΦ p q i r h) = square hΦ p q i r h := by
    simp only [cone, pullbackCone, coneSquare, Iso.inv_hom_id_assoc]
  rw [hs] at he
  exact he.symm.trans (square_source_vertex hΦ p q i r h)

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
