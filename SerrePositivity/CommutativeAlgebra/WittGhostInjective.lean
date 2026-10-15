module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Algebra.Regular.SMul

/-! # Injectivity of the Witt ghost map under p-regularity -/

@[expose] public section
namespace SerrePositivity

/-- Only injectivity of multiplication by p is needed for the Witt ghost map to be injective. -/
theorem witt_ghostMap_injective_of_mul_prime_injective
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    Function.Injective (WittVector.ghostMap (p := p) (R := A)) := by
  intro x y hxy
  apply WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrFun hxy n
    simp only [WittVector.ghostMap_apply, WittVector.ghostComponent_apply,
      aeval_wittPolynomial, Finset.sum_range_succ,
      Nat.sub_self, pow_zero, pow_one] at hn
    have hs : (∑ i ∈ Finset.range n, (p : A) ^ i * x.coeff i ^ p ^ (n - i)) =
        ∑ i ∈ Finset.range n, (p : A) ^ i * y.coeff i ^ p ^ (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih i (Finset.mem_range.mp hi)]
    rw [hs] at hn
    have hreg : IsSMulRegular A (p : A) := hp
    exact (hreg.pow n) (add_left_cancel hn)

end SerrePositivity
