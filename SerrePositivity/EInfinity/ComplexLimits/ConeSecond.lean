module
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimate

/-!
概要：元の有限集合の最初から二番目の点と、左切断が二点となる一意性を計算する。
方針：元の有限集合・全 cochain・切断の合成を端点の等式輸送と両立させる。
規約：中央相の切断和は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex


lemma erase_min_nonempty {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).Nonempty := by
  apply Finset.card_pos.mp
  have := Finset.card_erase_add_one (I.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  omega

def second {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) : Fin (n + 1) :=
  (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min' (erase_min_nonempty I hI)

lemma second_mem {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    second I hI ∈ I :=
  Finset.mem_of_mem_erase ((I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_mem _)

lemma min_lt_second {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) < second I hI := by
  have hne := (Finset.mem_erase.mp
    ((I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_mem (erase_min_nonempty I hI))).1
  exact lt_of_le_of_ne (I.min'_le _ (second_mem I hI)) hne.symm

lemma left_filter_second {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    I.filter (· ≤ second I hI) = {I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI), second I hI} := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiI, his⟩ := Finset.mem_filter.mp hi
    by_cases him : i = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
    · simp [him]
    · have hsi : second I hI ≤ i :=
        (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_le i (Finset.mem_erase.mpr ⟨him, hiI⟩)
      simp [le_antisymm his hsi]
  · intro hi
    rcases (show i = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) ∨ i = second I hI by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi) with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨I.min'_mem _, (min_lt_second I hI).le⟩
    · exact Finset.mem_filter.mpr ⟨second_mem I hI, le_rfl⟩

lemma left_card_two_iff_second {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hmj : I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) < j) :
    (I.filter (· ≤ j)).card = 2 ↔ j = second I hI := by
  constructor
  · intro hc
    have hsj : second I hI ≤ j := (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_le j
      (Finset.mem_erase.mpr ⟨hmj.ne.symm, hj⟩)
    have hl : IsLeast (↑(I.filter (· ≤ j)) : Set (Fin (n + 1)))
        (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) :=
      ⟨Finset.mem_filter.mpr ⟨I.min'_mem _, hmj.le⟩,
        fun _ h => I.min'_le _ (Finset.mem_filter.mp h).1⟩
    have hr : IsGreatest (↑(I.filter (· ≤ j)) : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hj, le_rfl⟩, fun _ h => (Finset.mem_filter.mp h).2⟩
    have hs : second I hI ∈ I.filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨second_mem I hI, hsj⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc hl hr] at hs
    rcases (show second I hI = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) ∨ second I hI = j by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hs) with hs | hs
    · exact False.elim ((min_lt_second I hI).ne hs.symm)
    · exact hs.symm
  · intro h
    subst j
    rw [left_filter_second]
    simp [(min_lt_second I hI).ne]

lemma second_lt_max {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hc : 3 ≤ I.card) : second I hI < I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
  have he : 2 ≤ (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).card := by
    have := Finset.card_erase_add_one (I.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    omega
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (I.min'_lt_max'_of_card (by omega)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty he)
  rw [hm]
  exact (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_lt_max'_of_card (by omega)

end SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
