module

public import SerrePositivity.CommutativeAlgebra.GradedHilbertSeries
public import SerrePositivity.CommutativeAlgebra.MonomialCounting
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The Hilbert series of a polynomial ring over a field

The monomial basis in each homogeneous degree identifies its dimension with a
multichoose number. Since module length over a field equals dimension, the Hilbert
series of the polynomial ring in `s` variables is `(1-X)⁻ˢ`, including `s = 0`.
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.PolynomialHilbertSeries

open MvPolynomial

variable (k : Type u) [Field k]

/-- The monomial basis of homogeneous polynomials of fixed total degree. -/
def homogeneousBasis (σ : Type v) (n : ℕ) :
    Module.Basis {m : σ →₀ ℕ // m.degree = n} k (homogeneousSubmodule σ k n) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact basisRestrictSupport k {m | m.degree = n}

/-- The dimension of the degree `n` component is the number of monomials of that degree. -/
theorem finrank_homogeneousSubmodule (σ : Type v) [Fintype σ] (n : ℕ) :
    Module.finrank k (homogeneousSubmodule σ k n) =
      Nat.multichoose (Fintype.card σ) n := by
  classical
  let : Fintype {m : σ →₀ ℕ // m.degree = n} := (Finsupp.finite_of_degree_eq n).fintype
  rw [Module.finrank_eq_card_basis (homogeneousBasis k σ n)]
  exact MonomialCounting.card_degree_eq_multichoose σ n

/-- Over a field, homogeneous degree length is its monomial count. -/
theorem length_homogeneousSubmodule (σ : Type v) [Fintype σ] (n : ℕ) :
    Module.length k (homogeneousSubmodule σ k n) =
      (Nat.multichoose (Fintype.card σ) n : ℕ∞) := by
  let : Module.Finite k (homogeneousSubmodule σ k n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg σ k n)
  rw [Module.length_eq_finrank, finrank_homogeneousSubmodule]

/-- Every homogeneous component has finite length. -/
theorem finiteLength_homogeneousSubmodule (σ : Type v) [Finite σ] (n : ℕ) :
    IsFiniteLength k (homogeneousSubmodule σ k n) := by
  let : Fintype σ := Fintype.ofFinite σ
  apply Module.length_ne_top_iff.mp
  rw [length_homogeneousSubmodule]
  exact ENat.natCast_ne_top _

/-- The inverse power of `1-X` has the multichoose coefficients, including exponent zero. -/
theorem coeff_invOneSubPow_eq_multichoose (s n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℚ s).val = (Nat.multichoose s n : ℚ) := by
  cases s with
  | zero =>
    cases n <;> simp [PowerSeries.invOneSubPow_zero, Nat.multichoose_zero_right,
      Nat.multichoose_zero_succ]
  | succ s =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      Nat.multichoose_eq]
    congr 1
    rw [show s + 1 + n - 1 = s + n by omega, Nat.choose_symm_add]

/-- The homogeneous-length series of the polynomial ring is `(1-X)⁻ˢ`. -/
theorem lengthSeries_homogeneousSubmodule (s : ℕ) :
    HilbertSerre.lengthSeries (homogeneousSubmodule (Fin s) k) =
      (PowerSeries.invOneSubPow ℚ s).val := by
  ext n
  rw [HilbertSerre.lengthSeries, PowerSeries.coeff_mk, length_homogeneousSubmodule,
    ENat.toNat_natCast, Fintype.card_fin, coeff_invOneSubPow_eq_multichoose]

end SerrePositivity.PolynomialHilbertSeries
