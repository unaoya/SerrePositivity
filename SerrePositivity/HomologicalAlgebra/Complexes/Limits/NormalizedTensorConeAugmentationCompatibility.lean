module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentationPositive
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentationEdge
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentationOrdinary

/-!
概要：元の実 cone の全斉次成分は、同じ対象ごとの augmentation と厳密に両立する。
方針：零次は混合・通常辺の合成式、他の次数は正次成分の消滅を使う。
規約：全有限集合・全次数の元の式を保つ。使われ方：終端 X を加えた二重 cone の HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeAugmentationAt_compose_pair {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b))).val
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b 0 hI ha hb hk) (add_zero 0) =
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c a))).val := by
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : (0 : Fin (n + 2)) ∈ I := by rw [ha]; exact I.min'_mem _
    exact eq_of_heq
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_compose_mixed_pair A X Y c I 0 b hI ha hb hk rfl h0)
  · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_compose_ordinary_pair A X Y c I a b hI ha hb hk ha0

lemma normalizedTensorConeAugmentationAt_compose {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b))).val
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk) (add_zero k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c a)) k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_compose_pair A X Y c I a b hI ha hb hk
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk0]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt_compose_of_card_ge_three A X Y c I a b k
      hI ha hb hk (by omega)

end SerrePositivity.ComplexLimits
