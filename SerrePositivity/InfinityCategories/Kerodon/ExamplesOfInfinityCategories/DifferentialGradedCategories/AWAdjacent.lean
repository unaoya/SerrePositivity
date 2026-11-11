module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWErasure
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-!
# 隣接する AW 切断の境界項の相殺の添字

概要：有限集合を昇順に並べ、隣接切断の前後の集合と符号を同定する。
方針：順序同型で Fin の隣接点の不等式へ戻し、最後にずらした有限和を相殺する。
規約：切断点の順序は標準境界と同じ昇順。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の切断点を削除する項の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α] {J : Finset α}

/-- 概要：次の切断点未満の集合は直前の切断点以下の集合である。
方針：元を昇順の番号へ戻すと、r<s+1 と r≤s の同値となる。
規約：集合の全ての点を順序同型 e で番号付けする。
使われ方：Kerodon 2.5.8（Tag 00S0） の隣接する二つの境界項の第一因子。 -/
lemma before_succ_eq_left {n : ℕ} (e : Fin (n + 1) ≃o J) (i : Fin n) :
    J.filter (· < (e i.succ).val) = J.filter (· ≤ (e i.castSucc).val) := by
  ext a
  by_cases ha : a ∈ J
  · simp only [Finset.mem_filter, ha, true_and]
    change (⟨a, ha⟩ : J) < e i.succ ↔ (⟨a, ha⟩ : J) ≤ e i.castSucc
    rw [← e.apply_symm_apply (⟨a, ha⟩ : J)]
    simp only [e.lt_iff_lt, e.le_iff_le]
    change (e.symm ⟨a, ha⟩).val < i.val + 1 ↔ (e.symm ⟨a, ha⟩).val ≤ i.val
    omega
  · simp [ha]

/-- 概要：直前の切断点より後の集合は次の切断点以上の集合である。
方針：接頭部分の隣接の式の補集合の条件を取る。
規約：集合の全ての点を順序同型 e で番号付けする。
使われ方：Kerodon 2.5.8（Tag 00S0） の隣接する二つの境界項の第二因子。 -/
lemma after_castSucc_eq_right {n : ℕ} (e : Fin (n + 1) ≃o J) (i : Fin n) :
    J.filter ((e i.castSucc).val < ·) = J.filter ((e i.succ).val ≤ ·) := by
  ext a
  by_cases ha : a ∈ J
  · have h := congrArg (fun S : Finset α ↦ a ∈ S) (before_succ_eq_left e i)
    simp only [Finset.mem_filter, ha, true_and] at h ⊢
    have h' := not_congr (Iff.of_eq h)
    simpa only [not_lt, not_le] using h'.symm
  · simp [ha]

/-- 概要：昇順の r 番目の点より前の点数は r である。
方針：順序同型の逆を使い、接頭集合と Fin の Iio の濃度を比較する。
規約：零番目の点では前の集合が空となる。
使われ方：Kerodon 2.5.8（Tag 00S0） の隣接切断の符号の比較。 -/
lemma card_before_orderIso {n : ℕ} (e : Fin (n + 1) ≃o J) (i : Fin (n + 1)) :
    (J.filter (· < (e i).val)).card = i.val := by
  classical
  have h : (J.filter (· < (e i).val)).card = (Finset.Iio i).card := by
    refine Finset.card_bij (fun a ha ↦ e.symm ⟨a, (Finset.mem_filter.mp ha).1⟩) ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_Iio]
      rw [← e.lt_iff_lt, e.apply_symm_apply]
      exact (Finset.mem_filter.mp ha).2
    · intro a ha b hb hab
      exact congrArg Subtype.val (e.symm.injective hab)
    · intro a ha
      refine ⟨(e a).val, Finset.mem_filter.mpr ⟨(e a).property, ?_⟩, ?_⟩
      · exact e.strictMono (Finset.mem_Iio.mp ha)
      · exact e.symm_apply_apply a
  exact h.trans (Fin.card_Iio i)

/-- 概要：隣接する切断点の標準境界符号は互いに負である。
方針：前の点数を番号に同定し、−1 のべきの漸化式を使う。
規約：符号は整数として比較する。
使われ方：HA 1.3.1.13 の切断点削除項の符号の相殺。 -/
lemma sign_succ_eq_neg {n : ℕ} (e : Fin (n + 1) ≃o J) (i : Fin n) :
    (-1 : ℤ) ^ (J.filter (· < (e i.succ).val)).card =
      -((-1 : ℤ) ^ (J.filter (· < (e i.castSucc).val)).card) := by
  rw [card_before_orderIso, card_before_orderIso]
  change (-1 : ℤ) ^ (i.val + 1) = -((-1 : ℤ) ^ i.val)
  rw [pow_succ, mul_neg_one]

/-- 概要：隣接する項が互いに負で端の項が零である二つの有限和は相殺する。
方針：一方は先頭、他方は末尾を分けて同じ Fin n の和へそろえる。
規約：値は任意の可換加法群でよい。
使われ方：Kerodon 2.5.8（Tag 00S0） の二つの対角境界和の相殺。 -/
lemma sum_adjacent_cancel {M : Type*} [AddCommGroup M] {n : ℕ}
    (G F : Fin (n + 1) → M) (hG : G 0 = 0) (hF : F (Fin.last n) = 0)
    (hstep : ∀ i : Fin n, G i.succ = -F i.castSucc) :
    (∑ i, G i) + ∑ i, F i = 0 := by
  rw [Fin.sum_univ_succ G, Fin.sum_univ_castSucc F, hG, hF, zero_add, add_zero]
  have h : (∑ i : Fin n, G i.succ) = -(∑ i : Fin n, F i.castSucc) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact hstep i
  rw [h, neg_add_cancel]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
