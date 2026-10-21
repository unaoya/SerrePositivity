module

public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientValueSquare
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare

/-!
概要：元の二脚の実 cospan 上に、頂点が元の E(A) である候補の実 ∞ 錐を構成する。
方針：四辺固定の正方形を join 錐へ移し、右辺・上辺と左下の頂点を保持する。
規約：任意の可換実現からの候補で、極限性は主張しない。使われ方：d8 の比較錐。
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
local instance coneSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable (Φ : StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

lemma square_source_vertex : squareVertex (square Φ p q i r h) 0 0 =
    coherentNerveVertex (value Φ A) := by
  have he := squareBottomEdge_source (square Φ p q i r h)
  rw [square_bottom] at he
  exact he.symm.trans ((congrArg (Sp.{u}.δ 1)
    (SSet.yonedaEquiv.apply_symm_apply (coherentNerveEdge (cSource Φ p q i)).edge)).trans
      (coherentNerveEdge (cSource Φ p q i)).src_eq)

def cospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} :=
  pullbackCospan (square Φ p q i r h)

def cone : JoinCone (cospan Φ p q i r h) := pullbackCone (square Φ p q i r h)

lemma cospan_C : horn₂₂.ι₀₂ ≫ cospan Φ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (valueMap Φ (laxQuotientCLeg p q r))).edge := by
  rw [cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge, square_right]

lemma cospan_D : horn₂₂.ι₁₂ ≫ cospan Φ p q i r h = SSet.yonedaEquiv.symm
    (coherentNerveEdge (valueMap Φ (laxQuotientDLeg p q r))).edge := by
  rw [cospan, pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge, square_top]

lemma cone_square : coneSquare (cone Φ p q i r h) = square Φ p q i r h := by
  simp only [cone, pullbackCone, coneSquare, Iso.inv_hom_id_assoc]

lemma cone_vertex : (cone Φ p q i r h).vertex = coherentNerveVertex (value Φ A) := by
  have he := FiberModel.coneSquare_apex (cone Φ p q i r h)
  rw [cone_square] at he
  exact he.symm.trans (square_source_vertex Φ p q i r h)

end SerrePositivity.KST.LocalizingInvariants.LaxQuotientSquare
