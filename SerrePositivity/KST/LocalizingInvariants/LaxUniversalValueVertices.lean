module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceValuePullback
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalValue
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h ≫ Φ

lemma vertex00 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (square Φ p q i r h) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A) := by
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_bottom, Equiv.apply_symm_apply,
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow i).src_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ A).symm

lemma vertex10 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (square Φ p q i r h) 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ (laxCategory p q)) := by
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_bottom, Equiv.apply_symm_apply,
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow i).tgt_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ (laxCategory p q)).symm

lemma vertex01 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (square Φ p q i r h) 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ Q) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_left, Equiv.apply_symm_apply,
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q i r)).tgt_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ Q).symm

lemma vertex11 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (square Φ p q i r h) 1 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ (laxCategory (𝟙 Q) (𝟙 Q))) := by
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare_right, Equiv.apply_symm_apply,
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (LaxUniversalDifference.exactLift p q r)).tgt_eq] at ht
  exact (congrArg (fun v => Φ.app (Opposite.op ⦋0⦌) v) ht.symm).trans
    (value_vertex Φ (laxCategory (𝟙 Q) (𝟙 Q))).symm

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalValue
