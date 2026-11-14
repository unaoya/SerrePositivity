module

public import SerrePositivity.EInfinity.IntervalCuts.InversionCounts

/-!
# 元の交差寄与と他色の先行数・小色の総数

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
指定位置の前の小色だけが二度現れることを、同じ元の順序と有限和で数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の一位置の交差寄与と二つの接頭条件の釣り合い（BF §2.2.6）。 -/
lemma word_cross_weight_term_balance {r l : ℕ} (w : Fin l → Fin r)
    (k : Fin r) (p : Fin l) (hp : w p = k) (j : Fin l) (a : ℕ) :
    (IntervalCuts.positionInversionTerm w j p + IntervalCuts.positionInversionTerm w p j) * a +
      2 * (if j < p ∧ w j < k then a else 0) =
    (if j < p ∧ w j ≠ k then a else 0) + (if w j < k then a else 0) := by
  by_cases hjp : j = p
  · subst j
    simp [IntervalCuts.positionInversionTerm, hp]
  · have hv : j.val ≠ p.val := fun he => hjp (Fin.ext he)
    unfold IntervalCuts.positionInversionTerm
    simp only [hp]
    split_ifs <;> simp_all <;> omega

/-- 元の全交差寄与に、二度数える先行小色を足した整数の釣り合い（BF §2.2.6）。 -/
lemma word_cross_weight_balance {r l : ℕ} (w : Fin l → Fin r)
    (k : Fin r) (p : Fin l) (hp : w p = k) (a : Fin l → ℕ) :
    (∑ j : {j : Fin l // w j ≠ k},
      (IntervalCuts.positionInversionTerm w j.val p +
        IntervalCuts.positionInversionTerm w p j.val) * a j.val) +
      2 * (∑ j : Fin l, if j < p ∧ w j < k then a j else 0) =
    (∑ j : Fin l, if j < p ∧ w j ≠ k then a j else 0) +
      (∑ j : Fin l, if w j < k then a j else 0) := by
  classical
  have hz : (∑ j : {j : Fin l // ¬w j ≠ k},
      (IntervalCuts.positionInversionTerm w j.val p +
        IntervalCuts.positionInversionTerm w p j.val) * a j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : w j.val = k := by simpa using j.property
    simp only [IntervalCuts.positionInversionTerm, hj, hp, lt_self_iff_false,
      and_false, ite_false, Nat.add_zero, Nat.zero_mul]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun j : Fin l => w j ≠ k)
    (fun j => (IntervalCuts.positionInversionTerm w j p +
      IntervalCuts.positionInversionTerm w p j) * a j)
  simp only [hz, Nat.add_zero] at hs
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin l))) rfl
    (fun j _ => word_cross_weight_term_balance w k p hp j (a j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at he
  rw [← hs] at he
  exact he

end SerrePositivity.EInfinity.SimplexCuts
