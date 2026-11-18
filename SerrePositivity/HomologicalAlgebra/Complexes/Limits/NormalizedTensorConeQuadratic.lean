module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeCutSupport

/-!
概要：実 cone の HA 右辺の非線形部分は一つの実切断合成だけである。
方針：元の内部点の全有限和で、最後から二番目以外の項を消す。
規約：元の符号と同じ切断合成を保つ。使われ方：混合 HA 方程式の最終合成項の照合。
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

lemma normalizedTensorConeData_quadratic_single {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).quadraticBoundary I a b k =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) •
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).cutCompose I a b k (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.quadraticBoundary
  apply Finset.sum_eq_single (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI)
  · intro j hj hne
    obtain ⟨hjI, haj, hjb⟩ := Finset.mem_filter.mp hj
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_cutCompose_of_ne_penultimate A X Y c I a b k hI ha hb hk
      j hjI haj hjb hne, smul_zero]
  · intro hnot
    exfalso
    apply hnot
    exact Finset.mem_filter.mpr ⟨_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_mem I hI,
      by rw [ha]; exact _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.min_lt_penultimate I hI hc,
      by rw [hb]; exact _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_lt_max I hI⟩

end SerrePositivity.ComplexLimits
