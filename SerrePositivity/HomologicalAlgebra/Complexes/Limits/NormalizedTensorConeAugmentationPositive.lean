module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeOrdinaryZero

/-!
概要：元の cone の全正次成分と同じ終端 augmentation の実合成は零である。
方針：通常成分は零、混合成分は同じ選択 cochain の augmentation 消滅へ戻す。
規約：元の実端点・符号・全有限集合を保つ。使われ方：二重 cone の高次方程式。
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

lemma normalizedTensorConeAugmentationAt_compose_of_card_ge_three {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b))).val
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk) (add_zero k) = 0 := by
  rw [_root_.SerrePositivity.ComplexLimits.complexPostcompose_graded]
  by_cases ha0 : a = 0
  · have h0 : (0 : Fin (n + 2)) ∈ I := by rw [← ha0, ha]; exact I.min'_mem _
    have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
    have hJtwo : 2 ≤ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card := by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega
    have hkJ : k = 1 - ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card : ℤ) := by
      have hs := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0
      omega
    have hp := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_postcompose_mixed
      A X Y c I a b k hI ha hb hk ha0 h0
    have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_augmentation_smul_zero
      A X Y c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k hJ hkJ hJtwo k.negOnePow
    have hx : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a = X := by
      change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c a = X
      rw [ha0, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_zero]
    have hzero : HEq (0 : GradedHom A ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a) X k)
        (0 : GradedHom A X X k) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx rfl rfl
    exact eq_of_heq (hp.trans ((heq_of_eq hz).trans hzero.symm))
  · rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_ordinary_zero A X Y c I a b k hI ha hb hk ha0 (by omega)]
    exact map_zero _

end SerrePositivity.ComplexLimits
