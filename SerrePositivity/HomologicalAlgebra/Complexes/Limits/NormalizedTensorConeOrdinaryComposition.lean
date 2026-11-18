module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeComponents
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexPostcomposeGraded
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：実 cone の通常辺と実 cochain の合成を、元の frame 射の後合成に同定する。
方針：通常成分を同じ閉零射に戻し、同じ端点輸送を保って dg 合成を計算する。
規約：元の frame 射・次数・cochain を保持する。
使われ方：最後の切断の実合成を元の普遍 cochain の像へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_hom_ordinary_closed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hab : a ≤ b) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b 0 hI ha hb hk)
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
          (c.map (homOfLE ((_root_.SerrePositivity.ComplexLimits.coneTailOrderHom n).monotone hab)))))).val := by
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_ordinary A X Y c I a b 0 hI ha hb hk ha0).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero _))

lemma normalizedTensorConeData_ordinary_compose {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hab : a ≤ b)
    (R : Complex A) (p : ℤ)
    (v : GradedHom A R ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a) p)
    (w : GradedHom A R
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (_root_.SerrePositivity.ComplexLimits.coneTailOrderHom n a))) p)
    (hv : HEq v w) :
    HEq (compose A ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b 0 hI ha hb hk) v (add_zero p))
      ((homPostcompose R ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE ((_root_.SerrePositivity.ComplexLimits.coneTailOrderHom n).monotone hab))))).f p w) := by
  have hb0 : b ≠ 0 := by
    have hlt : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
    exact ne_of_gt ((Fin.zero_le a).trans_lt hlt)
  have hy := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_ne_zero A X Y c a ha0
  have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_ne_zero A X Y c b hb0
  have hg := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_ordinary_closed A X Y c I a b hI ha hb hk ha0 hab
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) rfl hy hz rfl rfl rfl _ _ _ _ hg hv
    (add_zero p) (add_zero p)
  exact he.trans (heq_of_eq (_root_.SerrePositivity.ComplexLimits.complexPostcompose_graded A R _ p w))

end SerrePositivity.ComplexLimits
