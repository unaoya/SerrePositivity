module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Polynomial degrees from eventual growth on natural numbers

An eventual upper bound on evaluations bounds the degree of a polynomial with positive
leading coefficient. The comparison also permits an affine change of the natural-number
argument and multiplication by a constant. These results include constant polynomials and
require no positivity assumption on the polynomial giving the upper bound.
-/

@[expose] public section

open Polynomial Filter

namespace SerrePositivity.PolynomialGrowth

/-- An eventual upper bound on natural-number evaluations bounds the degree, provided the
polynomial being bounded has positive leading coefficient. -/
theorem natDegree_le_of_eventually_eval_le {P Q : ℚ[X]}
    (hP : 0 < P.leadingCoeff)
    (hPQ : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra! hdeg
  have hlt : Q.degree < P.degree := degree_lt_degree hdeg
  have hpos : 0 < (P - Q).degree := by
    rw [degree_sub_eq_left_of_degree_lt hlt]
    exact natDegree_pos_iff_degree_pos.mp ((Nat.zero_le Q.natDegree).trans_lt hdeg)
  have hlc : 0 ≤ (P - Q).leadingCoeff := by
    rw [leadingCoeff_sub_of_degree_lt hlt]
    exact hP.le
  have ht := ((P - Q).tendsto_atTop_of_leadingCoeff_nonneg hpos hlc).comp
    (tendsto_natCast_atTop_atTop (R := ℚ))
  obtain ⟨n, hn, hnpos⟩ := (hPQ.and (ht.eventually_gt_atTop 0)).exists
  change 0 < (P - Q).eval (n : ℚ) at hnpos
  rw [eval_sub] at hnpos
  exact (not_lt_of_ge hn) (sub_pos.mp hnpos)

/-- Affine substitution cannot increase degree beyond the original polynomial. This bound
also holds when the affine substitution is constant. -/
theorem natDegree_comp_affine_le (Q : ℚ[X]) (a b : ℚ) :
    (Q.comp (C a * X + C b)).natDegree ≤ Q.natDegree := by
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul_left Q.natDegree (natDegree_linear_le (a := a) (b := b))).trans_eq
      (Nat.mul_one _))

/-- Eventual comparison after any affine substitution of the natural-number argument gives
a degree bound. Neither the slope nor the leading coefficient of `Q` needs to be positive. -/
theorem natDegree_le_of_eventually_eval_affine_le {P Q : ℚ[X]}
    (hP : 0 < P.leadingCoeff) (a b : ℕ)
    (hPQ : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval ((a * n + b : ℕ) : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  apply (natDegree_le_of_eventually_eval_le hP (Q := Q.comp (C (a : ℚ) * X + C (b : ℚ))) ?_).trans
    (natDegree_comp_affine_le Q (a : ℚ) (b : ℚ))
  simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X, Nat.cast_add, Nat.cast_mul] using hPQ

/-- A constant multiple of an affine upper bound still bounds the degree. The multiplier may
be zero or negative; only the leading coefficient of `P` is assumed positive. -/
theorem natDegree_le_of_eventually_eval_le_mul_affine {P Q : ℚ[X]}
    (hP : 0 < P.leadingCoeff) (c : ℚ) (a b : ℕ)
    (hPQ : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ c * Q.eval ((a * n + b : ℕ) : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  apply (natDegree_le_of_eventually_eval_affine_le hP a b (Q := C c * Q) ?_).trans
    (natDegree_C_mul_le c Q)
  simpa only [eval_mul, eval_C] using hPQ

/-- A polynomial with positive leading coefficient is eventually positive on natural numbers,
including in degree zero. -/
theorem eventually_eval_pos {P : ℚ[X]} (hP : 0 < P.leadingCoeff) :
    ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℚ) := by
  by_cases hdeg : P.natDegree = 0
  · have h : 0 < P.coeff 0 := by simpa only [leadingCoeff, hdeg] using hP
    filter_upwards [] with n
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C]
    exact h
  · have ht := (P.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)) hP.le).comp
        (tendsto_natCast_atTop_atTop (R := ℚ))
    simpa only [Function.comp_apply] using ht.eventually_gt_atTop 0

/-- Translation preserves the leading term, so its finite difference has strictly smaller
degree. Polynomial degree, rather than natural degree, also accounts for the zero difference
of a constant polynomial. -/
theorem degree_sub_comp_sub_const_lt {P : ℚ[X]} (hP : P ≠ 0) (c : ℚ) :
    (P - P.comp (X - C c)).degree < P.degree := by
  apply degree_sub_lt_left (q := P.comp (X - C c)) ?_ hP ?_
  · symm
    rw [degree_comp (by simp), degree_X_sub_C, mul_one]
  · rw [leadingCoeff_comp (by simp), leadingCoeff_X_sub_C, one_pow, mul_one]

/-- If a positive-leading-coefficient polynomial bounds a backward finite difference of `P`,
then its degree is strictly less than that of `P`. The eventual inequality rules out constant
`P` automatically. The step `c` can be any natural number, including zero. -/
theorem natDegree_lt_of_eventually_eval_add_shift_le {P Q : ℚ[X]}
    (hQ : 0 < Q.leadingCoeff) (c : ℕ)
    (hPQ : ∀ᶠ n : ℕ in atTop,
      Q.eval (n : ℚ) + P.eval ((n - c : ℕ) : ℚ) ≤ P.eval (n : ℚ)) :
    Q.natDegree < P.natDegree := by
  let S : ℚ[X] := P - P.comp (X - C (c : ℚ))
  have hQS : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ S.eval (n : ℚ) := by
    filter_upwards [hPQ, eventually_ge_atTop c] with n hn hnc
    dsimp [S]
    rw [eval_sub, eval_comp, eval_sub, eval_X, eval_C, ← Nat.cast_sub hnc]
    exact le_sub_iff_add_le.mpr hn
  have hS : S ≠ 0 := by
    obtain ⟨n, hnpos, hnle⟩ := ((eventually_eval_pos hQ).and hQS).exists
    intro hzero
    rw [hzero, eval_zero] at hnle
    exact (not_lt_of_ge hnle) hnpos
  have hP : P ≠ 0 := by
    intro hzero
    apply hS
    simp [S, hzero]
  have hSP : S.natDegree < P.natDegree :=
    natDegree_lt_natDegree hS (degree_sub_comp_sub_const_lt hP (c : ℚ))
  exact (natDegree_le_of_eventually_eval_le hQ hQS).trans_lt hSP

end SerrePositivity.PolynomialGrowth
