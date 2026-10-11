module

public import SerrePositivity.CommutativeAlgebra.PolynomialGrowth
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Iterated backward differences of a polynomial

The `h`-fold backward difference of a polynomial of degree at most `h` is the constant
`h!` times its coefficient in degree `h`. The same value is eventually obtained from
any sequence eventually represented by that polynomial, even with truncated natural
subtraction in the definition of a backward difference.
-/

@[expose] public noncomputable section

namespace SerrePositivity.PolynomialFiniteDifference

open Polynomial Filter

/-- The backward difference `P(X)-P(X-1)`. -/
def backwardDifference : ℚ[X] →ₗ[ℚ] ℚ[X] := LinearMap.id - taylor (-1 : ℚ)

theorem backwardDifference_apply (P : ℚ[X]) :
    backwardDifference P = P - P.comp (X - C 1) := by
  change P - P.comp (X + C (-1 : ℚ)) = P - P.comp (X - C 1)
  rw [map_neg, sub_eq_add_neg (X : ℚ[X]) (C 1)]

/-- Taking one difference lowers a positive degree upper bound by one. -/
theorem natDegree_backwardDifference_le (P : ℚ[X]) (h : ℕ)
    (hP : P.natDegree ≤ h + 1) : (backwardDifference P).natDegree ≤ h := by
  by_cases hd : backwardDifference P = 0
  · simp [hd]
  have hp : P ≠ 0 := fun hp => hd (by simp [hp])
  have hlt := natDegree_lt_natDegree hd
    (by rw [backwardDifference_apply]
        exact PolynomialGrowth.degree_sub_comp_sub_const_lt hp 1)
  omega

/-- The top surviving coefficient of one difference is multiplied by the original degree. -/
theorem coeff_backwardDifference (P : ℚ[X]) (h : ℕ) (hP : P.natDegree ≤ h + 1) :
    (backwardDifference P).coeff h = (h + 1 : ℕ) * P.coeff (h + 1) := by
  have hhd : (hasseDeriv h P).natDegree ≤ 1 := by
    have := natDegree_hasseDeriv_le P h
    omega
  change (P - taylor (-1 : ℚ) P).coeff h = _
  rw [coeff_sub, taylor_coeff, eq_X_add_C_of_natDegree_le_one hhd,
    eval_add, eval_mul, eval_C, eval_X, eval_C, hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 h, Nat.choose_succ_self_right]
  ring

/-- The top iterated difference is constant, including the zero-degree case. -/
theorem iterate_backwardDifference_eq_C (h : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ h) :
    backwardDifference^[h] P = C ((h.factorial : ℚ) * P.coeff h) := by
  induction h generalizing P with
  | zero =>
    simpa only [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_mul] using
      eq_C_of_natDegree_le_zero hP
  | succ h ih =>
    rw [Function.iterate_succ_apply,
      ih (backwardDifference P) (natDegree_backwardDifference_le P h hP),
      coeff_backwardDifference P h hP, Nat.factorial_succ, Nat.cast_mul]
    congr 1
    ring

/-- Backward difference of a sequence, using natural-number subtraction. -/
def backwardDifferenceSeq (f : ℕ → ℚ) (n : ℕ) : ℚ := f n - f (n - 1)

/-- Eventual polynomial evaluation is preserved by taking one backward difference. -/
theorem eventually_backwardDifferenceSeq_eq_eval {f : ℕ → ℚ} {P : ℚ[X]}
    (hf : ∀ᶠ n : ℕ in atTop, f n = P.eval (n : ℚ)) :
    ∀ᶠ n : ℕ in atTop, backwardDifferenceSeq f n = (backwardDifference P).eval (n : ℚ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  apply eventually_atTop.mpr
  refine ⟨N + 1, fun n hn => ?_⟩
  have hNn : N ≤ n := by omega
  have hNm : N ≤ n - 1 := by omega
  have h1n : 1 ≤ n := by omega
  rw [backwardDifferenceSeq, hN n hNn, hN (n - 1) hNm, backwardDifference_apply,
    eval_sub, eval_comp, eval_sub, eval_X, eval_C, Nat.cast_sub h1n, Nat.cast_one]

/-- Iterated differences of an eventually polynomial sequence agree eventually with
evaluation of the polynomial's iterated differences. -/
theorem eventually_iterate_backwardDifferenceSeq_eq_eval {f : ℕ → ℚ} {P : ℚ[X]}
    (hf : ∀ᶠ n : ℕ in atTop, f n = P.eval (n : ℚ)) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (backwardDifferenceSeq^[h] f) n = (backwardDifference^[h] P).eval (n : ℚ) := by
  induction h with
  | zero => exact hf
  | succ h ih =>
    simpa only [Function.iterate_succ_apply'] using eventually_backwardDifferenceSeq_eq_eval ih

/-- Numerical form used for multiplicity: the eventual `h`th difference equals
`h!` times the degree-`h` coefficient of an eventual polynomial of degree at most `h`. -/
theorem eventually_iterate_backwardDifferenceSeq_eq_coeff {f : ℕ → ℚ} {P : ℚ[X]}
    (hf : ∀ᶠ n : ℕ in atTop, f n = P.eval (n : ℚ)) (h : ℕ) (hP : P.natDegree ≤ h) :
    ∀ᶠ n : ℕ in atTop,
      (backwardDifferenceSeq^[h] f) n = (h.factorial : ℚ) * P.coeff h := by
  simpa only [iterate_backwardDifference_eq_C h P hP, eval_C] using
    eventually_iterate_backwardDifferenceSeq_eq_eval hf h

end SerrePositivity.PolynomialFiniteDifference
