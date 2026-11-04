module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (Φ : StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} := pullbackCospan (square Φ p q i r h)

def cone : JoinCone (cospan Φ p q i r h) := pullbackCone (square Φ p q i r h)

lemma cospan_C : horn₂₂.ι₀₂ ≫ cospan Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r))).edge := by
  rw [cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge, square_right]

lemma cospan_D : horn₂₂.ι₁₂ ≫ cospan Φ p q i r h =
    SSet.yonedaEquiv.symm (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r))).edge := by
  rw [cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge, square_top]

lemma cone_square : coneSquare (cone Φ p q i r h) = square Φ p q i r h := by
  simp only [cone, pullbackCone, coneSquare, Iso.inv_hom_id_assoc]

lemma square_source_vertex : squareVertex (square Φ p q i r h) 0 0 =
    coherentNerveVertex (value Φ A) := by
  have he := squareBottomEdge_source (square Φ p q i r h)
  rw [square_bottom] at he
  exact he.symm.trans ((congrArg (Sp.{u}.δ 1)
    (SSet.yonedaEquiv.apply_symm_apply
      (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q))).edge)).trans
        (coherentNerveEdge (valueMap Φ i ≫ valueMap Φ (laxFst p q))).src_eq)

lemma cone_vertex : (cone Φ p q i r h).vertex = coherentNerveVertex (value Φ A) := by
  have he := FiberModel.coneSquare_apex (cone Φ p q i r h)
  rw [cone_square] at he
  exact he.symm.trans (square_source_vertex Φ p q i r h)

def coneComparison : FunctorIso
    (pullbackCone (LaxQuotientRelativeSquare.valueSquare p q i r h Φ)).val
    (cone Φ p q i r h).val :=
  FunctorIso.precomp (comparison Φ p q i r h) cospanConeSquareIso.hom

lemma cone_isLimit_of_relative (hQ : IsLimitCone
    (pullbackCone (LaxQuotientRelativeSquare.valueSquare p q i r h Φ))) :
    IsLimitCone (cone Φ p q i r h) :=
  IsLimitCone.of_functorIso hQ (coneComparison Φ p q i r h)

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientBFNormalization
