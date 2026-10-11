module

public import SerrePositivity.CommutativeAlgebra.GradedShiftMap
public import SerrePositivity.CommutativeAlgebra.PolynomialGrowth
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Algebra.Ring.GeomSum

/-! # Growth after imposing a nonzero homogeneous relation

The cumulative length function is the sum of the components in degrees below `n`.
An injective homogeneous map cancels one factor of the Hilbert-series denominator,
so the cumulative polynomial of its quotient has smaller degree.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open Polynomial Filter

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The cumulative numerical length of the components of degree strictly less than `n`. -/
def cumulativeLength (N : ℕ → Submodule R M) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, ((Module.length R (N i)).toNat : ℚ)

def cumulativeSeries (N : ℕ → Submodule R M) : PowerSeries ℚ :=
  PowerSeries.mk (cumulativeLength N)

lemma cumulativeLength_succ (N : ℕ → Submodule R M) (n : ℕ) :
    cumulativeLength N (n + 1) =
      cumulativeLength N n + ((Module.length R (N n)).toNat : ℚ) := by
  simp only [cumulativeLength, Finset.sum_range_succ]

/-- Passing from the component series to the cumulative series adds one denominator factor. -/
theorem one_sub_X_mul_cumulativeSeries (N : ℕ → Submodule R M) :
    (1 - PowerSeries.X) * cumulativeSeries N = PowerSeries.X * lengthSeries N := by
  ext n
  cases n with
  | zero => simp [cumulativeSeries, cumulativeLength]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      cumulativeSeries, lengthSeries, PowerSeries.coeff_mk, cumulativeLength_succ]
    ring

theorem cumulativeSeries_eq (N : ℕ → Submodule R M) :
    cumulativeSeries N = PowerSeries.X * lengthSeries N *
      (PowerSeries.invOneSubPow ℚ 1).val := by
  have hinv : (1 - PowerSeries.X) * (PowerSeries.invOneSubPow ℚ 1).val = 1 := by
    simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
      (PowerSeries.invOneSubPow ℚ 1).inv_val
  calc
    cumulativeSeries N = ((1 - PowerSeries.X) * cumulativeSeries N) *
        (PowerSeries.invOneSubPow ℚ 1).val := by rw [mul_right_comm, hinv, one_mul]
    _ = _ := by rw [one_sub_X_mul_cumulativeSeries]

/-- A rational component series with denominator exponent `s` gives a cumulative
polynomial of degree at most `s`. -/
theorem exists_cumulativePoly_of_lengthSeries (N : ℕ → Submodule R M) (s : ℕ) (Q : ℚ[X])
    (hseries : lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ s).val) :
    ∃ P : ℚ[X], (∀ᶠ n : ℕ in atTop, cumulativeLength N n = P.eval (n : ℚ)) ∧
      P.natDegree ≤ s := by
  let P := Polynomial.hilbertPoly (X * Q) (s + 1)
  have hs : cumulativeSeries N =
      (X * Q : ℚ[X]) * (PowerSeries.invOneSubPow ℚ (s + 1)).val := by
    rw [cumulativeSeries_eq, hseries, PowerSeries.invOneSubPow_add, Units.val_mul,
      Polynomial.coe_mul, Polynomial.coe_X]
    ring
  refine ⟨P, ?_, ?_⟩
  · filter_upwards [eventually_gt_atTop (X * Q).natDegree] with n hn
    have hc := congrArg (PowerSeries.coeff n) hs
    rw [cumulativeSeries, PowerSeries.coeff_mk,
      Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (s + 1) hn] at hc
    exact hc
  · by_cases hP : P = 0
    · simp [hP]
    · rw [Polynomial.natDegree_hilbertPoly_of_ne_zero hP]
      omega

/-- The numerator `1-X^d` cancels one denominator factor, without any formal division. -/
lemma one_sub_X_pow_mul_invOneSubPow (d s : ℕ) :
    (1 - PowerSeries.X ^ d) * (PowerSeries.invOneSubPow ℚ (s + 1)).val =
      ((∑ i ∈ Finset.range d, X ^ i : ℚ[X]) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ s).val := by
  have hg : (1 - PowerSeries.X ^ d : PowerSeries ℚ) =
      (1 - PowerSeries.X) * ((∑ i ∈ Finset.range d, X ^ i : ℚ[X]) : PowerSeries ℚ) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]
    have h := geom_sum_mul (PowerSeries.X : PowerSeries ℚ) d
    linear_combination h
  have hi : (1 - PowerSeries.X) * (PowerSeries.invOneSubPow ℚ 1).val = 1 := by
    simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
      (PowerSeries.invOneSubPow ℚ 1).inv_val
  rw [hg, PowerSeries.invOneSubPow_add, Units.val_mul]
  calc
    _ = ((∑ i ∈ Finset.range d, X ^ i : ℚ[X]) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ s).val *
        ((1 - PowerSeries.X) * (PowerSeries.invOneSubPow ℚ 1).val) := by ring
    _ = _ := by rw [hi, mul_one]

/-- The quotient by an injective homogeneous map has a cumulative polynomial with
one smaller degree bound than its source denominator exponent. -/
theorem exists_cumulativePoly_quotient_of_injective
    (N : ℕ → Submodule R M) [DirectSum.Decomposition N]
    (hfinite : ∀ n, IsFiniteLength R (N n)) (f : M →ₗ[R] M) (d : ℕ)
    (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + d)) (hf : Function.Injective f)
    (s : ℕ) (Q : ℚ[X])
    (hseries : lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ (s + 1)).val) :
    ∃ P : ℚ[X],
      (∀ᶠ n : ℕ in atTop, cumulativeLength (quotientGrade N f.range) n = P.eval (n : ℚ)) ∧
      P.natDegree ≤ s := by
  apply exists_cumulativePoly_of_lengthSeries (quotientGrade N f.range) s
    ((∑ i ∈ Finset.range d, X ^ i) * Q)
  rw [ShiftMap.lengthSeries_quotient_eq N f d hdegree hfinite hf, hseries,
    mul_left_comm, one_sub_X_pow_mul_invOneSubPow, Polynomial.coe_mul]
  ring

/-- Any eventually smaller cumulative function represented by a polynomial with positive
leading coefficient inherits the degree bound. -/
theorem natDegree_le_of_cumulative_quotient_bound
    (N : ℕ → Submodule R M) [DirectSum.Decomposition N]
    (hfinite : ∀ n, IsFiniteLength R (N n)) (f : M →ₗ[R] M) (d : ℕ)
    (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + d)) (hf : Function.Injective f)
    (s : ℕ) (Q : ℚ[X])
    (hseries : lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ (s + 1)).val)
    (P : ℚ[X]) (hP : 0 < P.leadingCoeff)
    (hbound : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ cumulativeLength (quotientGrade N f.range) n) :
    P.natDegree ≤ s := by
  obtain ⟨T, hT, hdeg⟩ :=
    exists_cumulativePoly_quotient_of_injective N hfinite f d hdegree hf s Q hseries
  apply (PolynomialGrowth.natDegree_le_of_eventually_eval_le hP ?_).trans hdeg
  filter_upwards [hbound, hT] with n hn hTn
  rwa [hTn] at hn

end SerrePositivity.HilbertSerre
