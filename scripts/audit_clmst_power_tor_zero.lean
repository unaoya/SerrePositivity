import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTorProduct
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorTorZero
import Mathlib.Util.AssertNoSorry

-- KL-A2f: standard torsion tests through the original holim to standard Tor.
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensor_scalar_zero_of_power_torsion_tests
assert_no_sorry SerrePositivity.DerivedCompletion.modulePowerTensorHolim_homology_comp_zero_of_power_torsion_tests
assert_no_sorry SerrePositivity.DerivedCompletion.derivedHomologyMap_comp_eq_zero_of_homologyMap_comp_eq_zero
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientDerivedTensor_homology_comp_zero_of_power_torsion_tests
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientTor_comp_zero_of_power_torsion_tests
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientTor_mul_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensor_scalar_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.modulePowerTensorHolim_homology_comp_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.derivedHomologyMap_comp_eq_zero_of_homologyMap_comp_eq_zero
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientDerivedTensor_homology_comp_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientTor_comp_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientTor_mul_zero_of_power_torsion_tests

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (a : R)
  (S : Type u) [CommRing S] [Algebra R S] (M : ModuleCat.{u} R) [Module.Finite R M]
  (hS : IsModuleComplete R a (ModuleCat.of R S))

-- Finite M may have arbitrary a-torsion. The two coefficient elements can differ.
example (i : ℕ) (c d : S)
    (hc : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0)
    (hd : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N (i + 1) d = 0) :
    torCoefficientScalarEndomorphism S M i (c * d) = 0 :=
  finiteCoefficientTor_mul_zero_of_power_torsion_tests a M S hS i c d hc hd

-- Finite-submodule reduction gives full test quantifiers and J²-annihilation.
assert_no_sorry SerrePositivity.DerivedCompletion.tor_mul_zero_of_power_torsion_tests
assert_no_sorry SerrePositivity.DerivedCompletion.tor_ideal_sq_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.tor_mul_zero_of_power_torsion_tests
#print axioms SerrePositivity.DerivedCompletion.tor_ideal_sq_zero_of_power_torsion_tests
