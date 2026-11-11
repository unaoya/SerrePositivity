module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleNoninjectiveCochains

/-!
概要：相の重複がある場合、元の最後／最初から二番目の切断合成を零へ戻す。
方針：元の非単射添字・同相の二点・切断の一意性を使う。
規約：主場合の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
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

lemma second_le_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hc : 3 ≤ I.card) : ConeHeadIndex.second I hI ≤ ConeHeadIndex.penultimate I hI :=
  (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_le _
    (Finset.mem_erase.mpr ⟨(ConeHeadIndex.min_lt_penultimate I hI hc).ne.symm,
      ConeHeadIndex.penultimate_mem I hI⟩)

lemma normalizedTensorTriangleData_penultimate_zero_of_second_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (haz : τ a = 0)
    (hs0 : τ (ConeHeadIndex.second I hI) = 0)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1) :
    (normalizedTensorTriangleData A X Y c τ).cutCompose I a b k
      (ConeHeadIndex.penultimate I hI) = 0 := by
  have haL : a ∈ I.filter (· ≤ ConeHeadIndex.penultimate I hI) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [ha]; exact I.min'_mem _
    · rw [ha]; exact (ConeHeadIndex.min_lt_penultimate I hI hc).le
  have hsL : ConeHeadIndex.second I hI ∈ I.filter (· ≤ ConeHeadIndex.penultimate I hI) :=
    Finset.mem_filter.mpr ⟨ConeHeadIndex.second_mem I hI, second_le_penultimate I hI hc⟩
  have hni := coneTriangleFrontIndex_not_injOn τ _ a (ConeHeadIndex.second I hI) haL hsL
    (by rw [ha]; exact (ConeHeadIndex.min_lt_second I hI).ne) haz hs0
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  split_ifs
  · rw [normalizedTensorTriangleData_homOrZero_front_noninj A X Y c τ _ a _ _ haz hp1 hni]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _
  · rfl

lemma normalizedTensorTrianglePinched_second_zero_of_penultimate_two {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hbt : τ b = 2)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (hp2 : τ (ConeHeadIndex.penultimate I hI) = 2) :
    (normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k
      (ConeHeadIndex.second I hI) = 0 := by
  have hpR : ConeHeadIndex.penultimate I hI ∈ I.filter (ConeHeadIndex.second I hI ≤ ·) :=
    Finset.mem_filter.mpr ⟨ConeHeadIndex.penultimate_mem I hI, second_le_penultimate I hI hc⟩
  have hbR : b ∈ I.filter (ConeHeadIndex.second I hI ≤ ·) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hb]; exact I.max'_mem _
    · rw [hb]; exact (ConeHeadIndex.second_lt_max I hI hc).le
  have hni := coneTriangleBackIndex_not_injOn τ _ (ConeHeadIndex.penultimate I hI) b hpR hbR
    (by rw [hb]; exact (ConeHeadIndex.penultimate_lt_max I hI).ne) hp2 hbt
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  split_ifs
  · rw [normalizedTensorTrianglePinched_homOrZero_back_noninj A X Y c τ _ _ b _ hs1 hbt hni]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _
  · rfl
end SerrePositivity.EInfinity.ComplexLimits
