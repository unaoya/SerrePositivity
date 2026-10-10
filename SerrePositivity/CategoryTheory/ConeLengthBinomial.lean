module

public import SerrePositivity.CategoryTheory.HomologicalConeLength
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Nat.Choose.Sum

/-! # 錐の長さの漸化式の二項展開

cochain 添字の q+j は、homological 添字 i=-q では i-j となる。
これは Laurent 多項式への (1+t)^e の乗算の係数公式である。
-/

@[expose] public section

namespace SerrePositivity

open scoped BigOperators

/-- cochain の次数を一つ進める線形作用素。 -/
def cochainLengthShift : Module.End ℝ (ℤ → ℝ) where
  toFun f q := f (q + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma cochainLengthShift_apply (f : ℤ → ℝ) (q : ℤ) :
    cochainLengthShift f q = f (q + 1) := rfl

@[simp] lemma cochainLengthShift_pow_apply (n : ℕ) (f : ℤ → ℝ) (q : ℤ) :
    (cochainLengthShift ^ n) f q = f (q + n) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, cochainLengthShift_apply, ih]
      congr 1
      omega

/-- 零写像の錐を e 回取る漸化式の二項係数による展開。 -/
lemma coneLength_binomial (n : ℕ) (f : ℤ → ℝ) (q : ℤ) :
    ((cochainLengthShift + 1) ^ n) f q =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * f (q + j) := by
  rw [(Commute.one_right cochainLengthShift).add_pow]
  simp only [one_pow, mul_one, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Module.End.natCast_apply,
    cochainLengthShift_pow_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]

/-- 各段が錐の漸化式を満たせば、最後の係数は二項公式で与えられる。 -/
lemma coneLength_binomial_of_recurrence (b : ℕ → ℤ → ℝ) (n : ℕ)
    (hb : ∀ k < n, ∀ q, b (k + 1) q = b k q + b k (q + 1)) (q : ℤ) :
    b n q = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * b 0 (q + j) := by
  have hi : ∀ k ≤ n, b k = ((cochainLengthShift + 1) ^ k) (b 0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
        funext q
        simpa only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
          Pi.add_apply, add_comm] using hb k (by omega) q
  rw [hi n le_rfl]
  exact coneLength_binomial n (b 0) q

/-- homological 添字では右辺は i-j となり、(1+t)^n の係数と一致する。 -/
lemma coneLength_binomial_homological (b : ℕ → ℤ → ℝ) (n : ℕ)
    (hb : ∀ k < n, ∀ q, b (k + 1) q = b k q + b k (q + 1)) (i : ℤ) :
    b n (-i) = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * b 0 (-(i - j)) := by
  simpa only [neg_sub, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using
    coneLength_binomial_of_recurrence b n hb (-i)

end SerrePositivity
