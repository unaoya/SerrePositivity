module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeAugmentation
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedAugmentationVertex

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeAugmentationAt_compose_mixed_pair {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (compose A (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
      (normalizedTensorConeAugmentationAt A X Y c b))).val
      ((normalizedTensorConeData A X Y c).hom I a b 0 hI ha hb hk) (add_zero 0))
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))).val := by
  rw [complexPostcompose_graded]
  have hJ := withoutFirst_nonempty hI h0
  have hc : (withoutFirst I).card = 1 := by have := card_withoutFirst I h0; omega
  have hp := normalizedTensorConeAugmentationAt_postcompose_mixed
    A X Y c I a b 0 hI ha hb hk ha0 h0
  simp only [Int.negOnePow_zero, one_smul] at hp
  exact hp.trans (heq_of_eq
    (normalizedTensorElementSelectedCochainAtMax_augmentation_vertex
      A X Y c (withoutFirst I) hJ hc))

end SerrePositivity.EInfinity.ComplexLimits
