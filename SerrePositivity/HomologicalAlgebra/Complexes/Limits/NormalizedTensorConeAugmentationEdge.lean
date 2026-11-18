module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedAugmentationVertex

/-!
概要：元の cone の先端からの辺と同じ終端 augmentation の合成は元の恒等 cochain である。
方針：符号零次元と一点選択 cochain の恒等像を、実端点の輸送付きで使う。
規約：元の実辺を保つ。使われ方：二重 cone の三点方程式。
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

lemma normalizedTensorConeAugmentationAt_compose_mixed_pair {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b))).val
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b 0 hI ha hb hk) (add_zero 0))
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))).val := by
  rw [_root_.SerrePositivity.ComplexLimits.complexPostcompose_graded]
  have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
  have hc : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card = 1 := by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega
  have hp := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_postcompose_mixed
    A X Y c I a b 0 hI ha hb hk ha0 h0
  simp only [Int.negOnePow_zero, one_smul] at hp
  exact hp.trans (heq_of_eq
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_augmentation_vertex
      A X Y c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) hJ hc))

end SerrePositivity.ComplexLimits
