module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceValuePullback
public import SerrePositivity.KST.LocalizingInvariants.TammeProjectionEquivalence

/-!
概要：普遍差の比較正方形の値の四頂点を、元の BF 値へ同定する。
方針：元の四辺の始点・終点を評価し、value の復号式を使う。
規約：元の E の同じ正方形を保持。使われ方：実積同値による全図式の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalValue
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (Φ : StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ

lemma vertex00 : squareVertex (square Φ p q i r h) 0 0 = coherentNerveVertex (value Φ A) := by
  have ht := squareBottomEdge_source (LaxUniversalDifference.comparisonSquare p q i r h)
  rw [LaxUniversalDifference.comparisonSquare_bottom, Equiv.apply_symm_apply,
    (stableArrow i).src_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ A).symm

lemma vertex10 : squareVertex (square Φ p q i r h) 1 0 =
    coherentNerveVertex (value Φ (laxCategory p q)) := by
  have ht := squareBottomEdge_target (LaxUniversalDifference.comparisonSquare p q i r h)
  rw [LaxUniversalDifference.comparisonSquare_bottom, Equiv.apply_symm_apply,
    (stableArrow i).tgt_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ (laxCategory p q)).symm

lemma vertex01 : squareVertex (square Φ p q i r h) 0 1 = coherentNerveVertex (value Φ Q) := by
  have ht := squareLeftEdge_target (LaxUniversalDifference.comparisonSquare p q i r h)
  rw [LaxUniversalDifference.comparisonSquare_left, Equiv.apply_symm_apply,
    (stableArrow (LaxUniversalDifference.kernelMap p q i r)).tgt_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ Q).symm

lemma vertex11 : squareVertex (square Φ p q i r h) 1 1 =
    coherentNerveVertex (value Φ (laxCategory (𝟙 Q) (𝟙 Q))) := by
  have ht := squareRightEdge_target (LaxUniversalDifference.comparisonSquare p q i r h)
  rw [LaxUniversalDifference.comparisonSquare_right, Equiv.apply_symm_apply,
    (stableArrow (LaxUniversalDifference.exactLift p q r)).tgt_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ (laxCategory (𝟙 Q) (𝟙 Q))).symm

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalValue
