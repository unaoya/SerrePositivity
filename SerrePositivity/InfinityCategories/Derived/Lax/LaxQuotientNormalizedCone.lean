module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare

/-!
概要：元の BF 合成二脚を持つ正方形の実錐と、比較道から得た錐との全図式比較。
方針：全正方形の同型を join 錐へ前合成し、元の頂点と cospan の二辺を回収する。
規約：極限性は未証明で、元の product fiber との比較が残る。使われ方：d8 の実比較錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
end SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
local instance instSimplicialCategoryOmegaSpectrum_1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} := pullbackCospan (square Φ p q i r h)

def cone : JoinCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan Φ p q i r h) := pullbackCone (square Φ p q i r h)

lemma cospan_C : horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientCLeg p q r))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge, square_right]

lemma cospan_D : horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge, square_top]

lemma cone_square : coneSquare (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone Φ p q i r h) = square Φ p q i r h := by
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone, pullbackCone, coneSquare, Iso.inv_hom_id_assoc]

lemma square_source_vertex : squareVertex (square Φ p q i r h) 0 0 =
    coherentNerveVertex (value Φ A) := by
  have he := squareBottomEdge_source (square Φ p q i r h)
  rw [square_bottom] at he
  exact he.symm.trans ((congrArg (Sp.{u}.δ 1)
    (SSet.yonedaEquiv.apply_symm_apply
      (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q))).edge)).trans
        (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q))).src_eq)

lemma cone_vertex : (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone Φ p q i r h).vertex = coherentNerveVertex (value Φ A) := by
  have he := FiberModel.coneSquare_apex (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone Φ p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone_square] at he
  exact he.symm.trans (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.square_source_vertex Φ p q i r h)

def coneComparison : FunctorIso
    (pullbackCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ)).val
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone Φ p q i r h).val :=
  FunctorIso.precomp (comparison Φ p q i r h) cospanConeSquareIso.hom

lemma cone_isLimit_of_relative (hQ : IsLimitCone
    (pullbackCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientRelativeSquare.valueSquare p q i r h Φ))) :
    IsLimitCone (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone Φ p q i r h) :=
  IsLimitCone.of_functorIso hQ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.coneComparison Φ p q i r h)

end SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cone := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.coneComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.coneComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.coneComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cone_isLimit_of_relative := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone_isLimit_of_relative

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cone_square := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone_square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cone_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cospan := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cospan_C := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan_C

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cospan_D := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan_D

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.instSimplicialCategoryOmegaSpectrum_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.instSimplicialCategoryOmegaSpectrum_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.instSimplicialCategoryOmegaSpectrum_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.square_source_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.square_source_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cone.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cone.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.coneComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.coneComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization.cospan.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientBFNormalization.cospan.eq_1
