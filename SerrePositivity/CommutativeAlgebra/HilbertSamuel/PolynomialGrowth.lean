module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.Polynomial.HilbertPoly

/-! # 多項式の値の増大と有限差分

## 概要

有理数係数の多項式について、十分先の値の比較から次数と最高次係数を比べる補題と、
多項式の値の数列の有限差分（反復すると定数＝最高次係数の階乗倍になる）を集める。

## 方針

値の比較は最高次項の支配による。差分は前進差分 `fwdDiff`（Mathlib/Algebra/Group/ForwardDiff）で表す。

## 規約

ℚ 係数。Hilbert–Samuel の多項式と累積長さの多項式に共通の道具。

## 使われ方

Hilbert 級数・Samuel 多項式の次数の評価（`HilbertSamuel/*`）、Koszul 重複度の極限（B2）。
-/

@[expose] public noncomputable section

universe u v w

section Growth

open Polynomial Filter

namespace SerrePositivity

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

end SerrePositivity

end Growth

section FiniteDifference

namespace SerrePositivity

open Polynomial Filter fwdDiff

/-- 十分先で一致する数列は、十分先で同じ反復前進差分を持つ。 -/
theorem eventually_fwdDiff_iter_eq {f g : ℕ → ℚ} (hfg : ∀ᶠ n : ℕ in atTop, f n = g n) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop, (Δ_[1]^[h] f) n = (Δ_[1]^[h] g) n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfg
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hN _ (by simp; omega)]

/-- 自然数の上で多項式の値を取る数列の前進差分は、多項式の前進差分の値。 -/
theorem fwdDiff_iter_eval_natCast (P : ℚ[X]) (h n : ℕ) :
    (Δ_[1]^[h] (fun m : ℕ => P.eval (m : ℚ))) n = (Δ_[1]^[h] P.eval) (n : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- 十分先で次数 `h` 以下の多項式 `P` の値に一致する数列の `h` 回の前進差分は、十分先で `h! · P_h`。 -/
theorem eventually_fwdDiff_iter_eq_factorial_mul_coeff {f : ℕ → ℚ} {P : ℚ[X]}
    (hf : ∀ᶠ n : ℕ in atTop, f n = P.eval (n : ℚ)) (h : ℕ) (hP : P.natDegree ≤ h) :
    ∀ᶠ n : ℕ in atTop, (Δ_[1]^[h] f) n = (h.factorial : ℚ) * P.coeff h := by
  filter_upwards [eventually_fwdDiff_iter_eq hf h] with n hn
  rw [hn, fwdDiff_iter_eval_natCast]
  rcases hP.lt_or_eq with hlt | heq
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt, coeff_eq_zero_of_natDegree_lt hlt]
    simp
  · subst heq
    rw [P.fwdDiff_iter_degree_eq_factorial, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl

end SerrePositivity

end FiniteDifference

section PartialSums

namespace SerrePositivity

open Polynomial Filter

/-- `(1 - X) · (1 - X)⁻¹ = 1`（ℚ 係数の冪級数）。 -/
lemma one_sub_X_mul_invOneSubPow_one :
    (1 - PowerSeries.X : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ 1).val = 1 := by
  simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
    (PowerSeries.invOneSubPow ℚ 1).inv_val

/-- 部分和の級数は元の級数に `X / (1 - X)` を掛けたもの。 -/
theorem mk_partialSum_eq (a : ℕ → ℚ) :
    PowerSeries.mk (fun n => ∑ i ∈ Finset.range n, a i) =
      PowerSeries.X * PowerSeries.mk a * (PowerSeries.invOneSubPow ℚ 1).val := by
  have h : (1 - PowerSeries.X) * PowerSeries.mk (fun n => ∑ i ∈ Finset.range n, a i) =
      PowerSeries.X * PowerSeries.mk a := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
      simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
        Finset.sum_range_succ]
      ring
  calc PowerSeries.mk (fun n => ∑ i ∈ Finset.range n, a i)
      = ((1 - PowerSeries.X) * PowerSeries.mk (fun n => ∑ i ∈ Finset.range n, a i)) *
          (PowerSeries.invOneSubPow ℚ 1).val := by
        rw [mul_right_comm, one_sub_X_mul_invOneSubPow_one, one_mul]
    _ = _ := by rw [h]

/-- 数列 `a` の級数が `Q / (1 - X)^s` なら、部分和 `∑_{i<n} a i` は十分先で次数 `s` 以下の多項式の値。
累積長さと Samuel 関数（Hilbert 関数の部分和）の多項式性に共通の議論。 -/
theorem exists_poly_eventually_eq_partialSum (a : ℕ → ℚ) (s : ℕ) (Q : ℚ[X])
    (hseries : PowerSeries.mk a = Q * (PowerSeries.invOneSubPow ℚ s).val) :
    ∃ P : ℚ[X], (∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range n, a i = P.eval (n : ℚ)) ∧
      P.natDegree ≤ s := by
  let P := Polynomial.hilbertPoly (X * Q) (s + 1)
  have hs : PowerSeries.mk (fun n => ∑ i ∈ Finset.range n, a i) =
      (X * Q : ℚ[X]) * (PowerSeries.invOneSubPow ℚ (s + 1)).val := by
    rw [mk_partialSum_eq, hseries, PowerSeries.invOneSubPow_add, Units.val_mul,
      Polynomial.coe_mul, Polynomial.coe_X]
    ring
  refine ⟨P, ?_, ?_⟩
  · filter_upwards [eventually_gt_atTop (X * Q).natDegree] with n hn
    have hc := congrArg (PowerSeries.coeff n) hs
    rwa [PowerSeries.coeff_mk,
      Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (s + 1) hn] at hc
  · by_cases hP : P = 0
    · simp [hP]
    · rw [Polynomial.natDegree_hilbertPoly_of_ne_zero hP]
      omega

end SerrePositivity

end PartialSums

section EventuallyPositive

namespace SerrePositivity

open Polynomial Filter

/-- 十分先の自然数で正の値を取る有理数係数の多項式は、最高次係数が正。 -/
theorem leadingCoeff_pos_of_eventually_eval_pos {P : ℚ[X]}
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℚ)) : 0 < P.leadingCoeff := by
  by_cases hdeg : P.natDegree = 0
  · obtain ⟨n, hn⟩ := hpos.exists
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C] at hn
    simpa only [leadingCoeff, hdeg] using hn
  · by_contra! hlc
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)) hlc).comp
        (tendsto_natCast_atTop_atTop (R := ℚ))
    obtain ⟨n, hn, hn'⟩ := (hpos.and (ht.eventually_lt_atBot 0)).exists
    exact (lt_trans hn hn').false

end SerrePositivity

end EventuallyPositive
