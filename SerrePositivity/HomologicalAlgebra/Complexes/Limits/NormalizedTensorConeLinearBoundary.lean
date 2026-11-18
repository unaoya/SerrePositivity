module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeErasedLast
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeBoundarySum
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRhs

/-!
概要：始点と終端を含む実 cone の線形境界を、同じ普遍 cochain の内部削除和へ移す。
方針：全内部点を後続元で再添字付けし、各削除成分と符号を同じ座標へ同定する。
規約：同じ全有限和を保持する。使われ方：終端切断を戻す混合 HA 方程式の右辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_linearBoundary_reindex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).linearBoundary I a b k =
      ∑ j : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) j.val •
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).homOrZero (I.erase j.val.succ) a b (k + 1)
        else 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I 0 (Fin.last (n + 1)) := by rw [ha0, hbl]
  rw [hi, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.sum_interior_zero_last]
  simp only [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.sign_succ]

lemma normalizedTensorConeData_linearBoundary_mixed_last {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (hJ : 2 ≤ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card)
    (hkJ : k = 1 - ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card : ℤ)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).linearBoundary I a b k)
      (∑ j : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) j.val • ((k + 1).negOnePow •
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component
            ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase j.val) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
            (by have := Finset.card_erase_add_one j.property; omega)) else 0) := by
  have hx : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a = X := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c a = X
    rw [ha0, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_zero]
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj b =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)) := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c b = _
    rw [hbl]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ A X Y c (Fin.last n)
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_linearBoundary_reindex A X Y c I a b k ha0 hbl]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq hx hy
  intro j
  by_cases hj : j.val < Fin.last n
  · simp only [ite_eq_left hj]
    have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_erased_succ_mixed_last A X Y c I a b k hI ha hb hk
      ha0 hbl h0 j.val (by simpa only [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst, Finset.mem_filter, Finset.mem_univ,
        true_and] using j.property) (by rw [hbl]; exact Fin.succ_lt_succ_iff.mpr hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
      (by have := Finset.card_erase_add_one j.property; omega)
    have ht : ∀ (x y x' y' : Complex A) (hx : x = x') (hy : y = y')
        (v : GradedHom A x y (k + 1)) (w : GradedHom A x' y' (k + 1)),
        HEq v w → HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) j.val • v)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) j.val • w) := by
      intro x y x' y' hx hy v w hv
      subst x'
      subst y'
      cases eq_of_heq hv
      rfl
    exact ht _ _ _ _ hx hy _ _ he
  · simp only [ite_eq_right hj]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl

end SerrePositivity.ComplexLimits
