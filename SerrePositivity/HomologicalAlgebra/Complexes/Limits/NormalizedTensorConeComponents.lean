module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeData

/-!
概要：実 cone データの混合成分と通常成分を、元の二つの構成射へ回収する。
方針：始点の二分岐を評価し、端点の移送を異種等号として保持する。
規約：同じ選択 cochain と同じ通常単体を使う。
使われ方：実 cone の全方程式と面への制限の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_hom_ordinary {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex A X Y c).toSimplexData.hom I a b k hI ha hb hk) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData]
  rw [dite_eq_right ha0]
  exact cast_heq _ _

lemma normalizedTensorConeData_hom_mixed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk)
      (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0) (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega)) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData]
  rw [dite_eq_left ha0]
  exact cast_heq _ _

end SerrePositivity.ComplexLimits
