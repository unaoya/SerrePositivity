module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMiddleRightSupport
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMiddleLeftSupport

/-!
概要：元の二つの中央相の全符号付き切断和を、最後／最初から二番目の一項へ戻す。
方針：元の実 cochain・次数・部分集合と切断の一意性を使う。
規約：残る一項同士の比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_middle_sum {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hbt : τ b = 2) :
    (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (fun j => τ j = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      (normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j) =
    if τ (ConeHeadIndex.penultimate I hI) = 1 then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (ConeHeadIndex.penultimate I hI) •
        (normalizedTensorTriangleData A X Y c τ).cutCompose I a b k
          (ConeHeadIndex.penultimate I hI) else 0 := by
  have hp : ConeHeadIndex.penultimate I hI ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b := by
    refine Finset.mem_filter.mpr ⟨ConeHeadIndex.penultimate_mem I hI, ?_⟩
    constructor
    · rw [ha]; exact ConeHeadIndex.min_lt_penultimate I hI hc
    · rw [hb]; exact ConeHeadIndex.penultimate_lt_max I hI
  rw [Finset.sum_filter]
  apply Finset.sum_eq_single (ConeHeadIndex.penultimate I hI)
  · intro j hj hne
    by_cases hj1 : τ j = 1
    · rw [ite_eq_left hj1,
        normalizedTensorTriangleData_cutCompose_middle_ne_penultimate A X Y c τ I hI a b j k
          hb (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2.2 hbt hj1 hne, smul_zero]
    · exact ite_eq_right hj1
  · intro hnp
    exact False.elim (hnp hp)

lemma normalizedTensorTrianglePinched_middle_sum {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) :
    (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (fun j => τ j = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      (normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j) =
    if τ (ConeHeadIndex.second I hI) = 1 then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (ConeHeadIndex.second I hI) •
        (normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k
          (ConeHeadIndex.second I hI) else 0 := by
  have hp : ConeHeadIndex.second I hI ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b := by
    refine Finset.mem_filter.mpr ⟨ConeHeadIndex.second_mem I hI, ?_⟩
    constructor
    · rw [ha]; exact ConeHeadIndex.min_lt_second I hI
    · rw [hb]; exact ConeHeadIndex.second_lt_max I hI hc
  rw [Finset.sum_filter]
  apply Finset.sum_eq_single (ConeHeadIndex.second I hI)
  · intro j hj hne
    by_cases hj1 : τ j = 1
    · rw [ite_eq_left hj1,
        normalizedTensorTrianglePinched_cutCompose_middle_ne_second A X Y c τ I hI a b j k
          ha (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2.1 hj1 hne, smul_zero]
    · exact ite_eq_right hj1
  · intro hnp
    exact False.elim (hnp hp)
end SerrePositivity.EInfinity.ComplexLimits
