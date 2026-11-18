module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSigns
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# 元の連続部分語の区切り数と行順位の差

Berger–Fresse §1.2.2・§1.2.5・§2.2.6、M14 L12a の C452。
既存 lineRank の濃度を一位置ずつ増やし、同じ有限和を数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 一位置進んだ元の順位は、その位置の区切りの分だけ増える（BF §1.2.2）。 -/
lemma lineRank_succ_at {n l : ℕ} (v : Fin l → Fin n) (j : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (j.val + 1) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v j.val + if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v j then 1 else 0 := by
  let S := Finset.univ.filter (fun z : Fin l => z.val < j.val ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v z)
  have hs : Finset.univ.filter (fun z : Fin l => z.val < j.val + 1 ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v z) =
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v j then insert j S else S := by
    ext z
    by_cases hz : z = j
    · subst z
      by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v j <;>
        simp [Finset.mem_filter, S, hc]
    · have hne : z.val ≠ j.val := fun he => hz (Fin.ext he)
      have hlt : z.val < j.val + 1 ↔ z.val < j.val := by omega
      by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v j <;>
        simp [Finset.mem_filter, S, hc, hz, hlt]
  have hj : j ∉ S := by simp [S, Finset.mem_filter]
  change (Finset.univ.filter (fun z : Fin l =>
    z.val < j.val + 1 ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v z)).card = S.card + _
  rw [hs]
  by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v j
  · rw [ite_eq_left hc, ite_eq_left hc, Finset.card_insert_of_notMem hj]
  · rw [ite_eq_right hc, ite_eq_right hc, Nat.add_zero]

/-- 元の区切りの連続和は、同じ両端の行順位の差（BF §1.2.5）。 -/
lemma sum_consecutive_caesuraIndicators {n l : ℕ} (v : Fin l → Fin n)
    (a L : ℕ) (h : a + L ≤ l) :
    (∑ z : Fin L, if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v
        ⟨a + z.val, by have hz := z.isLt; omega⟩ then 1 else 0 : ℕ) +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (a + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hp := ih (by omega : a + L ≤ l)
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lineRank_succ_at v (⟨a + L, by omega⟩ : Fin l)
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (a + L + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (a + L) +
      (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v ⟨a + L, by omega⟩ then 1 else 0) at hs
    rw [Nat.add_assoc a L 1] at hs
    omega

/-- 同じ有限和を、末尾以外と元の末尾の一項に分ける（BF §2.2.6 の補助）。 -/
lemma sum_fin_last {L : ℕ} (hL : 0 < L) (F : Fin L → ℕ) :
    (∑ z, F z) = (∑ z : Fin (L - 1), F ⟨z.val, by have hz := z.isLt; omega⟩) +
      F ⟨L - 1, by omega⟩ := by
  cases L with
  | zero => omega
  | succ L =>
    simp only [Nat.add_sub_cancel, Fin.sum_univ_castSucc]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
