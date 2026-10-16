import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerComparison
import Mathlib.Util.AssertNoSorry

-- KL-A2c: actual finite-coefficient torsion error tower and standard quotient comparison.
assert_no_sorry SerrePositivity.exists_power_torsion_bound_of_noetherian
assert_no_sorry SerrePositivity.exists_power_torsion_bound_of_finite
assert_no_sorry SerrePositivity.smul_eq_zero_tensor_of_flat_of_smul_kernel
assert_no_sorry SerrePositivity.flat_tensor_power_torsion_bound
assert_no_sorry SerrePositivity.DerivedCompletion.powerTorsionComplex_holim_acyclic_of_term_bound
assert_no_sorry SerrePositivity.DerivedCompletion.powerImageComplex_holim_acyclic_of_term_bound
assert_no_sorry SerrePositivity.DerivedCompletion.powerCokernelReconstruction_quasiIso_of_term_bound
assert_no_sorry SerrePositivity.DerivedCompletion.koszulPowerCokernelComparison_quasiIso_of_term_bound
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientTensorModel
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientTensorModel_has_torsion_bound
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientTensorModel_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.finiteCoefficientPowerComparison_quasiIso
#print axioms SerrePositivity.exists_power_torsion_bound_of_noetherian
#print axioms SerrePositivity.exists_power_torsion_bound_of_finite
#print axioms SerrePositivity.smul_eq_zero_tensor_of_flat_of_smul_kernel
#print axioms SerrePositivity.flat_tensor_power_torsion_bound
#print axioms SerrePositivity.DerivedCompletion.powerTorsionComplex_holim_acyclic_of_term_bound
#print axioms SerrePositivity.DerivedCompletion.powerImageComplex_holim_acyclic_of_term_bound
#print axioms SerrePositivity.DerivedCompletion.powerCokernelReconstruction_quasiIso_of_term_bound
#print axioms SerrePositivity.DerivedCompletion.koszulPowerCokernelComparison_quasiIso_of_term_bound
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientTensorModel
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientTensorModel_has_torsion_bound
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientTensorModel_isComplete
#print axioms SerrePositivity.DerivedCompletion.finiteCoefficientPowerComparison_quasiIso

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- The common comparison includes scalar zero, with arbitrary finite test modules.
example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (C M : ModuleCat.{u} R) [Module.Finite R M] :
    QuasiIso (koszulPowerCokernelComparison (0 : R) (finiteCoefficientTensorModel R C M)) :=
  finiteCoefficientPowerComparison_quasiIso R 0 C M
    (isModuleComplete_of_pow_smul_zero R 0 C 1 (by intro x; simp))

-- The torsion bound is a bound on M, without regularity of the scalar or a flat M.
example {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (a : R) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0 :=
  exists_power_torsion_bound_of_finite a
