module

public import SerrePositivity.EInfinity.PowerOperation.MayCyclicNorm

/-!
# May の係数ノルム恒等式の基底環への移送

May, Proposition 2.3(ii)。F_p の係数恒等式を指定環準同型で移す補助。
宇宙を持ち上げた F_p の上でも同じ係数計算を使うために置く。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open Polynomial
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p]

lemma mayNormPolynomial_baseField :
    (X - 1 : Polynomial k) ^ (p - 1) = ∑ i ∈ Finset.range p, (X : Polynomial k) ^ i := by
  have h := congrArg (Polynomial.map (ZMod.castHom (dvd_refl p) k))
    (mayNormPolynomial p)
  simpa only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_sum, Polynomial.map_X] using h

lemma mayNormPolynomial_baseField_aeval {A : Type*} [Ring A] [Algebra k A] (t : A) :
    (t - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, t ^ i := by
  have h := congrArg (Polynomial.aeval t) (mayNormPolynomial_baseField p k)
  simpa only [map_pow, map_sub, map_one, map_sum, aeval_X] using h

lemma mayCyclicNorm_baseField {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k (MayCyclicGroup.{u} p) V) :
    ρ.norm = (ρ (mayCyclicGenerator p) - 1) ^ (p - 1) := by
  calc
    ρ.norm = ∑ i : Fin p, ρ (mayCyclicGenerator p ^ (i : ℕ)) := by
      exact (Equiv.sum_comp (mayCyclicPowerEquiv p) (fun g => ρ g)).symm
    _ = ∑ i ∈ Finset.range p, ρ (mayCyclicGenerator p) ^ i := by
      simp only [map_pow, Fin.sum_univ_eq_sum_range]
    _ = (ρ (mayCyclicGenerator p) - 1) ^ (p - 1) :=
      (mayNormPolynomial_baseField_aeval p k (ρ (mayCyclicGenerator p))).symm

end SerrePositivity.EInfinity.PowerOperation
