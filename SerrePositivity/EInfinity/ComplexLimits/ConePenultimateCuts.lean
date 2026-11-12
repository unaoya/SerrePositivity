module
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimate
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Signs

/-!
概要：最後に残る切断の左集合と符号、始点を除く削除添字を計算する。
方針：最大点を除いた集合の最大性と、後続元での所属条件を使う。
規約：元の有限集合・順序・符号を保つ。使われ方：実非線形項と終端削除 cochain の一致。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex


lemma left_filter_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    I.filter (· ≤ penultimate I hI) = I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiI, hip⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_erase.mpr ⟨?_, hiI⟩
    intro him
    rw [him] at hip
    exact (penultimate_lt_max I hI).not_ge hip
  · intro hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hi).2,
      (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' i hi⟩

lemma filter_above_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    I.filter (penultimate I hI < ·) = {I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)} := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiI, hpi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_singleton.mpr
    by_contra him
    have hip : i ≤ penultimate I hI :=
      (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' i (Finset.mem_erase.mpr ⟨him, hiI⟩)
    exact hpi.not_ge hip
  · intro hi
    rw [Finset.mem_singleton.mp hi]
    exact Finset.mem_filter.mpr ⟨I.max'_mem _, penultimate_lt_max I hI⟩

lemma sign_penultimate {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (penultimate I hI) = -1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, filter_above_penultimate, Finset.card_singleton, Int.natCast_one,
    Int.negOnePow_one]

lemma withoutFirst_erase_succ {n : ℕ} (I : Finset (Fin (n + 2))) (j : Fin (n + 1)) :
    withoutFirst (I.erase j.succ) = (withoutFirst I).erase j := by
  ext i
  simp [withoutFirst]

end SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
