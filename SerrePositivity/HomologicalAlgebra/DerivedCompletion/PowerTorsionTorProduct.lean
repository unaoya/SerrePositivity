module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorTorZero
public import SerrePositivity.HomologicalAlgebra.TorCoefficientIdeal
public import SerrePositivity.HomologicalAlgebra.TorFiniteCoefficients

/-! # Products of torsion-tested coefficient elements act trivially on all Tor tests

Filtered finite-submodule reduction retains arbitrary test modules. The ideal
conclusion is J²-annihilation; this does not assert J-annihilation without a
further argument.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- No finiteness or completeness assumption is imposed on the final test module. -/
lemma tor_mul_zero_of_power_torsion_tests
    (hS : IsModuleComplete R a (ModuleCat.of R S)) (i : ℕ) (c d : S)
    (hc : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0)
    (hd : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N (i + 1) d = 0)
    (M : ModuleCat.{u} R) : torCoefficientScalarEndomorphism S M i (c * d) = 0 := by
  apply torCoefficientScalarEndomorphism_eq_zero_of_finite S i (c * d) _ M
  intro N hN
  letI := hN
  exact finiteCoefficientTor_mul_zero_of_power_torsion_tests a N S hS i c d hc hd

/-- The square of the tested ideal kills all positive Tor, with the full test
quantifiers preserved. An extension-closure or idempotence input is not hidden. -/
lemma tor_ideal_sq_zero_of_power_torsion_tests
    (hS : IsModuleComplete R a (ModuleCat.of R S)) (J : Ideal S)
    (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → ∀ i : ℕ, 0 < i →
        ∀ c ∈ J, torCoefficientScalarEndomorphism S N i c = 0)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i)
    (c : S) (hc : c ∈ J ^ 2) : torCoefficientScalarEndomorphism S M i c = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj M
  have hmul : J * J ≤ coefficientFunctorAnnihilator (C := S) F := by
    apply Ideal.mul_le.mpr
    intro x hx y hy
    exact tor_mul_zero_of_power_torsion_tests a S hS i x y
      (fun N k hk hN => hTor N k hk hN i hi x hx)
      (fun N k hk hN => hTor N k hk hN (i + 1) (Nat.succ_pos _) y hy) M
  exact hmul (by simpa only [pow_two] using hc)

end SerrePositivity.DerivedCompletion
