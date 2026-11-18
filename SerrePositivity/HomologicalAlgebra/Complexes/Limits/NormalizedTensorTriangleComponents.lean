module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleData

/-!
概要：実混合データの全 cochain を元の三分岐の成分へ異種等号で回収する。
方針：元の引き戻し単体・実射・端点の等式輸送を保持する。
規約：全 HA 方程式は別工程。使われ方：大域評価三角形の実混合単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_hom_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b ≠ 2) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData]
  rw [dite_eq_right hbt]
  exact cast_heq _ _

lemma normalizedTensorTriangleData_hom_back {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b = 2) (haz : τ a ≠ 0) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData]
  rw [dite_eq_left hbt, dite_eq_right haz]
  exact cast_heq _ _

lemma normalizedTensorTriangleData_hom_pinched {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b = 2) (haz : τ a = 0) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk) := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData]
  rw [dite_eq_left hbt, dite_eq_left haz]
  exact cast_heq _ _

end SerrePositivity.ComplexLimits
