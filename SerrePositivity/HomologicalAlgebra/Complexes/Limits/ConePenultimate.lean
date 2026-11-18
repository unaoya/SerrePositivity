module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeWithoutFirst

/-!
概要：最後の二点だけを持つ右切断を、元の有限集合の最後から二番目の点に同定する。
方針：最大点を除いた集合の最大点と、二点集合の端点の一意性を使う。
規約：元の順序と有限集合を保つ。使われ方：混合 HA 右辺に一つだけ残る切断。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits.ConeHeadIndex


lemma erase_max_nonempty {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).Nonempty := by
  apply Finset.card_pos.mp
  have := Finset.card_erase_add_one (I.max'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  omega

def penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) : Fin (n + 1) :=
  (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).max' (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.erase_max_nonempty I hI)

lemma penultimate_mem {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI ∈ I :=
  Finset.mem_of_mem_erase ((I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).max'_mem _)

lemma penultimate_lt_max {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI < I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
  have hne := (Finset.mem_erase.mp
    ((I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).max'_mem (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.erase_max_nonempty I hI))).1
  exact lt_of_le_of_ne (I.le_max' _ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_mem I hI)) hne

lemma right_filter_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    I.filter (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI ≤ ·) = {_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI, I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)} := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiI, hpi⟩ := Finset.mem_filter.mp hi
    by_cases him : i = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
    · simp [him]
    · have hip : i ≤ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI :=
        (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' i (Finset.mem_erase.mpr ⟨him, hiI⟩)
      simp [le_antisymm hip hpi]
  · intro hi
    rcases (show i = _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI ∨ i = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi) with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_mem I hI, le_rfl⟩
    · exact Finset.mem_filter.mpr ⟨I.max'_mem _, (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_lt_max I hI).le⟩

lemma right_card_two_iff_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hjm : j < I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) :
    (I.filter (j ≤ ·)).card = 2 ↔ j = _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI := by
  constructor
  · intro hc
    have hjp : j ≤ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI := (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' j
      (Finset.mem_erase.mpr ⟨hjm.ne, hj⟩)
    have hl : IsLeast (↑(I.filter (j ≤ ·)) : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hj, le_rfl⟩, fun _ h => (Finset.mem_filter.mp h).2⟩
    have hr : IsGreatest (↑(I.filter (j ≤ ·)) : Set (Fin (n + 1)))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) :=
      ⟨Finset.mem_filter.mpr ⟨I.max'_mem _, hjm.le⟩,
        fun _ h => I.le_max' _ (Finset.mem_filter.mp h).1⟩
    have hp : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI ∈ I.filter (j ≤ ·) :=
      Finset.mem_filter.mpr ⟨_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_mem I hI, hjp⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc hl hr] at hp
    rcases (show _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI = j ∨ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hp) with hp | hp
    · exact hp.symm
    · exact False.elim ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_lt_max I hI).ne hp)
  · intro h
    subst j
    rw [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.right_filter_penultimate]
    simp [(_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_lt_max I hI).ne]

lemma min_lt_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hc : 3 ≤ I.card) : I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) < _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI := by
  have he : 2 ≤ (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).card := by
    have := Finset.card_erase_add_one (I.max'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    omega
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (I.min'_lt_max'_of_card (by omega)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty he)
  rw [hm]
  exact (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_lt_max'_of_card (by omega)

end SerrePositivity.ComplexLimits.ConeHeadIndex
