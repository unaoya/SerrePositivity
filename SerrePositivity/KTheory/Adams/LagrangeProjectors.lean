module

public import SerrePositivity.KTheory.Adams.WeightPolynomial
public import Mathlib.LinearAlgebra.Lagrange

/-! # Lagrange projectors for an operator annihilated by distinct linear factors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity
namespace Adams
open Polynomial
variable {E : Type u} [Field E] {ι : Type v} [DecidableEq ι]
variable (s : Finset ι) (v : ι → E)

lemma lagrange_factor (i : ι) (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i =
      C (∏ j ∈ s.erase i, (v i - v j)⁻¹) * ∏ j ∈ s, (X - C (v j)) := by
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor]
  rw [Finset.prod_mul_distrib, ← map_prod, mul_left_comm,
    Finset.mul_prod_erase s (fun j => (X : E[X]) - C (v j)) hi]

variable {M : Type w} [AddCommGroup M] [Module E M]
variable (T : Module.End E M)

def lagrangeProjector (i : ι) : Module.End E M := aeval T (Lagrange.basis s v i)

lemma lagrangeProjector_eigen (i : ι) (hi : i ∈ s) (x : M)
    (hx : (aeval T (∏ j ∈ s, (X - C (v j)))) x = 0) :
    T (lagrangeProjector s v T i x) = v i • lagrangeProjector s v T i x := by
  apply sub_eq_zero.mp
  have he := congrArg (fun Q : E[X] => (aeval T Q) x) (lagrange_factor s v i hi)
  simp only [map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply] at he
  change T (lagrangeProjector s v T i x) - v i • lagrangeProjector s v T i x =
    (∏ j ∈ s.erase i, (v i - v j)⁻¹) • (aeval T (∏ j ∈ s, (X - C (v j)))) x at he
  exact he.trans (by rw [hx, smul_zero])

lemma sum_lagrangeProjector (hv : Set.InjOn v s) (hs : s.Nonempty) (x : M) :
    (∑ i ∈ s, lagrangeProjector s v T i x) = x := by
  have he := congrArg (fun Q : E[X] => (aeval T Q) x) (Lagrange.sum_basis hv hs)
  simpa only [lagrangeProjector, map_sum, LinearMap.sum_apply, map_one,
    Module.End.one_apply] using he

lemma polynomial_on_eigenvector (a : E) (x : M) (hx : T x = a • x) (Q : E[X]) :
    (aeval T Q) x = Q.eval a • x := by
  have hp : ∀ n : ℕ, (T ^ n) x = a ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, ← pow_succ]
  induction Q using Polynomial.induction_on' with
  | add Q Q' hQ hQ' => simp only [map_add, LinearMap.add_apply, eval_add, add_smul, hQ, hQ']
  | monomial n b =>
    simp only [aeval_monomial, Module.End.mul_apply, eval_monomial]
    change b • ((T ^ n) x) = (b * a ^ n) • x
    rw [hp, smul_smul]

lemma lagrangeProjector_on_eigenvector_self (hv : Set.InjOn v s) (i : ι) (hi : i ∈ s)
    (x : M) (hx : T x = v i • x) : lagrangeProjector s v T i x = x := by
  rw [lagrangeProjector, polynomial_on_eigenvector T (v i) x hx,
    Lagrange.eval_basis_self hv hi, one_smul]

lemma lagrangeProjector_on_eigenvector_ne (i j : ι) (hj : j ∈ s) (hne : i ≠ j)
    (x : M) (hx : T x = v j • x) : lagrangeProjector s v T i x = 0 := by
  rw [lagrangeProjector, polynomial_on_eigenvector T (v j) x hx,
    Lagrange.eval_basis_of_ne hne hj, zero_smul]

lemma lagrangeProjector_idem (hv : Set.InjOn v s) (i : ι) (hi : i ∈ s)
    (hT : ∀ x : M, (aeval T (∏ j ∈ s, (X - C (v j)))) x = 0) :
    lagrangeProjector s v T i * lagrangeProjector s v T i = lagrangeProjector s v T i := by
  ext x
  exact lagrangeProjector_on_eigenvector_self s v T hv i hi _
    (lagrangeProjector_eigen s v T i hi x (hT x))

lemma lagrangeProjector_orthogonal (i j : ι) (hj : j ∈ s) (hne : i ≠ j)
    (hT : ∀ x : M, (aeval T (∏ k ∈ s, (X - C (v k)))) x = 0) :
    lagrangeProjector s v T i * lagrangeProjector s v T j = 0 := by
  ext x
  exact lagrangeProjector_on_eigenvector_ne s v T i j hj hne _
    (lagrangeProjector_eigen s v T j hj x (hT x))

end Adams
end SerrePositivity
