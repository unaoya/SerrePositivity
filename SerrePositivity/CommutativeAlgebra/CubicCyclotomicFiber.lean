module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicAlgebra
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # A simple irreducible factor of the cubic cyclotomic closed fiber -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open Polynomial
variable {K : Type u} [Field K]

lemma cubicCyclotomicPolynomial_derivative (htwo : (2 : K) = 0) :
    (cubicCyclotomicPolynomial K).derivative = 1 := by
  simp only [cubicCyclotomicPolynomial, derivative_add, derivative_X_pow,
    derivative_X, derivative_one, Nat.cast_ofNat, htwo, C_0, zero_mul, zero_add, add_zero]

lemma cubicCyclotomicPolynomial_separable (htwo : (2 : K) = 0) :
    (cubicCyclotomicPolynomial K).Separable := by
  rw [separable_def, cubicCyclotomicPolynomial_derivative htwo]
  exact isCoprime_one_right

/-- A chosen monic factor is coprime to its cofactor, whether linear or quadratic. -/
lemma exists_cubicCyclotomic_coprime_factor (htwo : (2 : K) = 0) :
    ∃ g h : K[X], g.Monic ∧ Irreducible g ∧
      cubicCyclotomicPolynomial K = g * h ∧ IsCoprime g h ∧ IsField (AdjoinRoot g) := by
  have hnu : ¬ IsUnit (cubicCyclotomicPolynomial K) := by
    intro hu
    have hd := natDegree_eq_zero_of_isUnit hu
    rw [cubicCyclotomicPolynomial_natDegree K] at hd
    omega
  obtain ⟨g, hg, hi, hdvd⟩ := exists_monic_irreducible_factor (cubicCyclotomicPolynomial K) hnu
  obtain ⟨h, hh⟩ := hdvd
  have hd : g.derivative * h + g * h.derivative = 1 := by
    rw [← derivative_mul, ← hh]
    exact cubicCyclotomicPolynomial_derivative htwo
  refine ⟨g, h, hg, hi, hh, ?_, (AdjoinRoot.isField_iff_irreducible).mpr hi⟩
  refine ⟨h.derivative, g.derivative, ?_⟩
  calc
    h.derivative * g + g.derivative * h = g.derivative * h + g * h.derivative := by ring
    _ = 1 := hd

end SerrePositivity
