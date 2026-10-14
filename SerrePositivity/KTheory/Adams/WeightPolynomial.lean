module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-! # Adams weight polynomials and intertwining of polynomial evaluations -/

@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity
namespace Adams
open Polynomial
variable (E : Type u) [CommRing E]

def weightPolynomial (p c d : ℕ) : E[X] :=
  ∏ j ∈ Finset.Icc c d, (X - C ((p : E) ^ j))

lemma weightPolynomial_top (p d : ℕ) : weightPolynomial E p (d + 1) d = 1 := by
  have he : Finset.Icc (d + 1) d = ∅ := Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self d)
  rw [weightPolynomial, he, Finset.prod_empty]

lemma weightPolynomial_succ (p c d : ℕ) (hc : c ≤ d) :
    weightPolynomial E p c d = weightPolynomial E p (c + 1) d * (X - C ((p : E) ^ c)) := by
  have he : Finset.Icc c d = insert c (Finset.Icc (c + 1) d) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [weightPolynomial, he, Finset.prod_insert (by simp)]
  exact mul_comm _ _

variable {E}
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module E M]
  [AddCommGroup N] [Module E N]

lemma endomorphism_pow_intertwine (T : Module.End E M) (U : Module.End E N)
    (f : M →ₗ[E] N) (hf : ∀ x, f (T x) = U (f x)) (n : ℕ) (x : M) :
    f ((T ^ n) x) = (U ^ n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [hf, ih]

/-- Intertwining operators intertwines every polynomial in them, without finite dimension. -/
lemma polynomial_intertwine (T : Module.End E M) (U : Module.End E N)
    (f : M →ₗ[E] N) (hf : ∀ x, f (T x) = U (f x)) (Q : E[X]) (x : M) :
    f ((aeval T Q) x) = (aeval U Q) (f x) := by
  induction Q using Polynomial.induction_on' with
  | add Q Q' hQ hQ' =>
    simp only [map_add, LinearMap.add_apply, hQ, hQ']
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply]
    change f (a • ((T ^ n) x)) = a • ((U ^ n) (f x))
    rw [map_smul, endomorphism_pow_intertwine T U f hf]

end Adams
end SerrePositivity
