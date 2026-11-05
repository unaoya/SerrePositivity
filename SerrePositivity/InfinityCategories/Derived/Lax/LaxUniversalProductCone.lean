module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
local instance instSimplicialCategoryOmegaSpectrum_1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

lemma square_bottom : squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge
      (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_bottom_of_boundary _ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_boundary hΦ p q i r h)

lemma square_top : squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q)))).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_top_of_boundary _ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_boundary hΦ p q i r h)

lemma square_left : squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r))).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_left_of_boundary _ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_boundary hΦ p q i r h)

lemma square_right : squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r)).edge :=
  _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.square_right_of_boundary _ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_boundary hΦ p q i r h)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} := pullbackCospan (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h)

def cone : JoinCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan hΦ p q i r h) := pullbackCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h)

lemma cone_isLimit : IsLimitCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone hΦ p q i r h) := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_isPullback hΦ p q i r h

lemma cospan_product : horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_right]

lemma cospan_diagonal : horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan hΦ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q)))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_top]

lemma square_source_vertex : squareVertex (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h) 0 0 =
    coherentNerveVertex (value Φ A) := by
  have he := squareBottomEdge_source (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_bottom] at he
  exact he.symm.trans ((congrArg (Sp.{u}.δ 1) (SSet.yonedaEquiv.apply_symm_apply
    (coherentNerveEdge
      (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)).edge)).trans
        (coherentNerveEdge
          (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i)).src_eq)

lemma cone_vertex : (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone hΦ p q i r h).vertex = coherentNerveVertex (value Φ A) := by
  have he := FiberModel.coneSquare_apex (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone hΦ p q i r h)
  have hs : coneSquare (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone hΦ p q i r h) = _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h := by
    simp only [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone, pullbackCone, coneSquare, Iso.inv_hom_id_assoc]
  rw [hs] at he
  exact he.symm.trans (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_source_vertex hΦ p q i r h)

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cone := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cone_isLimit := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone_isLimit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cone_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cospan := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cospan_diagonal := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan_diagonal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cospan_product := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan_product

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.instSimplicialCategoryOmegaSpectrum_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.instSimplicialCategoryOmegaSpectrum_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.instSimplicialCategoryOmegaSpectrum_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_left := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_right := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_source_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_source_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_top := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cone.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cone.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.cospan.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.cospan.eq_1
