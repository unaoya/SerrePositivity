module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTrianglePrincipalInjectivity
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimateCuts

/-!
概要：主場合の中央部分集合の濃度と、最初から二番目の切断の符号を計算する。
方針：元の部分集合・全添字像・実評価射と端点の等式輸送を保持する。
規約：二つの主切断の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits


lemma middle_card_add_two {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2) :
    (I.filter (fun i => τ i = 1)).card + 2 = I.card := by
  have he : I.filter (fun i => τ i = 1) =
      (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiI, hi1⟩ := Finset.mem_filter.mp hi
      apply Finset.mem_erase.mpr
      constructor
      · intro h
        have ht := congrArg τ h
        rw [hi1, hbt] at ht
        exact (by decide : (1 : Fin 3) ≠ 2) ht
      · apply Finset.mem_erase.mpr
        refine ⟨?_, hiI⟩
        intro h
        have ht := congrArg τ h
        rw [hi1, haz] at ht
        exact (by decide : (1 : Fin 3) ≠ 0) ht
    · intro hi
      obtain ⟨hmax, hi⟩ := Finset.mem_erase.mp hi
      obtain ⟨hmin, hiI⟩ := Finset.mem_erase.mp hi
      have h0 : τ i ≠ 0 := fun hz => hmin (eq_min_of_second_one τ I hI hs1 i hiI hz)
      have h2 : τ i ≠ 2 := fun ht => hmax (eq_max_of_penultimate_one τ I hI hp1 i hiI ht)
      exact Finset.mem_filter.mpr ⟨hiI, by omega⟩
  have hne : I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) ≠ I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
    intro h
    have ht := congrArg τ h
    rw [hbt, haz] at ht
    exact (by decide : (2 : Fin 3) ≠ 0) ht
  have hb := Finset.card_erase_add_one
    (Finset.mem_erase.mpr ⟨hne, I.max'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)⟩)
  have ha := Finset.card_erase_add_one (I.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  rw [he]
  omega

lemma sign_second_card {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (ConeHeadIndex.second I hI) = ((I.card : ℤ) - 2).negOnePow := by
  have hleft : (I.filter (· ≤ ConeHeadIndex.second I hI)).card = 2 := by
    rw [ConeHeadIndex.left_filter_second]
    simp [(ConeHeadIndex.min_lt_second I hI).ne]
  have hcard := Finset.card_filter_add_card_filter_not (s := I)
    (fun i => i ≤ ConeHeadIndex.second I hI)
  rw [hleft] at hcard
  simp only [not_le] at hcard
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign
  congr 1
  omega
end SerrePositivity.EInfinity.ComplexLimits
