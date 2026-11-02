module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import SerrePositivity.KTheory.Adams.Family

/-! # Adams の重みの多項式と射影

## 概要

Adams の重みの多項式と、相異なる一次式で消される作用素の Lagrange 射影、正則性や高さの上界を課す前の重みの射影を与え、多項式の Adams 作用素が台の拡大と可換なこと、積で重みが足し合わされ相異なる重みは共存しないことを示す。

## 方針

射影は Lagrange 補間の多項式で作り、作用素の多項式として可換性を示す。

## 規約

正則性や高さの上界はここでは課さない。

## 使われ方

`Adams/PureWeight`・`Adams/CyclicTwo`・`Adams/CyclicThree`。
-/

@[expose] public noncomputable section

universe u v w

section WeightPolynomialPart

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

end WeightPolynomialPart

section LagrangeProjectorsPart

set_option backward.isDefEq.respectTransparency false
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
    (aeval T Q) x = Q.eval a • x :=
  Module.End.aeval_apply_of_mem_apply_eq_smul hx

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

end LagrangeProjectorsPart

section PolynomialNaturalityPart

namespace SerrePositivity.Adams
open Polynomial
variable {R : Type u} [CommRing R] {E : Type v} [CommRing E] {p : ℕ}

lemma SupportedAdams.polynomial_enlarge (A : SupportedAdams R E p)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (Q : E[X])
    (x : K0WithSupport.Coefficients E Z) :
    (aeval (A.operation W) Q) (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h ((aeval (A.operation Z) Q) x) :=
  (polynomial_intertwine _ _ (K0WithSupport.coefficientEnlarge E h)
    (fun y => (A.enlarge h y).symm) Q x).symm

end SerrePositivity.Adams

end PolynomialNaturalityPart

section WeightOperatorsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [Field E] [CharZero E] {p : ℕ}

lemma natPow_injective (hp : 2 ≤ p) : Function.Injective (fun j : ℕ => (p : E) ^ j) := by
  intro i j he
  change (p : E) ^ i = (p : E) ^ j at he
  have hn : p ^ i = p ^ j := by exact_mod_cast he
  exact Nat.pow_right_injective hp hn

def SupportedAdams.weightProjector (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c d j : ℕ) :
    Module.End E (K0WithSupport.Coefficients E Z) :=
  lagrangeProjector (Finset.Icc c d) (fun j => (p : E) ^ j) (A.operation Z) j

lemma SupportedAdams.sum_weightProjector (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c d : ℕ) (hc : c ≤ d)
    (x : K0WithSupport.Coefficients E Z) :
    (∑ j ∈ Finset.Icc c d, A.weightProjector Z c d j x) = x :=
  sum_lagrangeProjector _ _ _ (natPow_injective (E := E) A.two_le).injOn
    ⟨c, Finset.mem_Icc.mpr ⟨le_refl c, hc⟩⟩ x

omit [CharZero E] in
lemma SupportedAdams.weightProjector_enlarge (A : SupportedAdams R E p)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (c d j : ℕ)
    (x : K0WithSupport.Coefficients E Z) :
    A.weightProjector W c d j (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (A.weightProjector Z c d j x) :=
  A.polynomial_enlarge h _ x

end Adams
end SerrePositivity

end WeightOperatorsPart

section WeightProductPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [Field E] {p : ℕ}
namespace SupportedAdams

lemma cup_eigen (A : SupportedAdams R E p)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (i j : ℕ)
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z)
    (hx : A.operation Y x = (p : E) ^ i • x)
    (hy : A.operation Z y = (p : E) ^ j • y) :
    A.operation (Y ⊓ Z) (K0WithSupport.coefficientCup E x y) =
      (p : E) ^ (i + j) • K0WithSupport.coefficientCup E x y := by
  rw [A.cup, hx, hy]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, pow_add, mul_comm]

lemma eigen_enlarge (A : SupportedAdams R E p)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (i : ℕ)
    (x : K0WithSupport.Coefficients E Z) (hx : A.operation Z x = (p : E) ^ i • x) :
    A.operation W (K0WithSupport.coefficientEnlarge E h x) =
      (p : E) ^ i • K0WithSupport.coefficientEnlarge E h x := by
  rw [A.enlarge, hx, map_smul]

lemma cup_enlarge_eigen (A : SupportedAdams R E p)
    {Y Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Y ⊓ Z ≤ W) (i j : ℕ)
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z)
    (hx : A.operation Y x = (p : E) ^ i • x)
    (hy : A.operation Z y = (p : E) ^ j • y) :
    A.operation W (K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y)) =
      (p : E) ^ (i + j) •
        K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y) :=
  A.eigen_enlarge h (i + j) _ (A.cup_eigen i j x y hx hy)

lemma eigen_eq_zero_of_ne (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (a b : E)
    (x : K0WithSupport.Coefficients E Z) (hx : A.operation Z x = a • x)
    (hy : A.operation Z x = b • x) (hne : a ≠ b) : x = 0 := by
  have hz : (a - b) • x = 0 := by rw [sub_smul, ← hx, ← hy, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

variable [CharZero E]

lemma eigen_eq_zero_of_weight_ne (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (i j : ℕ)
    (x : K0WithSupport.Coefficients E Z) (hx : A.operation Z x = (p : E) ^ i • x)
    (hy : A.operation Z x = (p : E) ^ j • x) (hne : i ≠ j) : x = 0 :=
  A.eigen_eq_zero_of_ne Z _ _ x hx hy
    (fun he => hne (natPow_injective (E := E) A.two_le he))

end SupportedAdams
end Adams
end SerrePositivity

end WeightProductPart
