module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：実 cone の通常側の正次成分は零である。
方針：元の閉 nerve の非零次数の消滅を、同じ端点の移送で回収する。
規約：同じ生データと任意の有限集合を保持する。
使われ方：混合 HA 方程式の右因子が二点以外となる切断合成の消去。
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

lemma normalizedTensorConeData_hom_ordinary_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hc : I.card ≠ 2) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk = 0 := by
  have hb0 : b ≠ 0 := by
    have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
    exact ne_of_gt ((Fin.zero_le a).trans_lt hab)
  have hx : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex A X Y c).obj a := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex_obj]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_ne_zero A X Y c a ha0
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj b =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex A X Y c).obj b := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex_obj]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_ne_zero A X Y c b hb0
  have hz : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex A X Y c).hom I a b k hI ha hb hk = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k (by omega)
  have he0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k) (l := k) hx hy rfl
  exact eq_of_heq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_ordinary A X Y c I a b k hI ha hb hk ha0).trans
     ((heq_of_eq hz).trans he0.symm))

end SerrePositivity.ComplexLimits
