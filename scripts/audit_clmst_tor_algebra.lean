import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraComplete
import Mathlib.Util.AssertNoSorry

-- Actual coefficient-algebra Tor, original scalar actions and completeness.
assert_no_sorry SerrePositivity.algebraResolutionTorComparison
assert_no_sorry SerrePositivity.algebraResolutionTorComparison_coefficient_scalar
assert_no_sorry SerrePositivity.torAlgebraComparison
assert_no_sorry SerrePositivity.torAlgebraComparison_coefficient_scalar
assert_no_sorry SerrePositivity.torAlgebraComparison_scalar_eq_zero_iff
assert_no_sorry SerrePositivity.torAlgebraComparison_scalar_zero_iff_forall
assert_no_sorry SerrePositivity.torAlgebraComparison_restricted_annihilator_iff
assert_no_sorry SerrePositivity.DerivedCompletion.torModule_isModuleComplete_of_finite
assert_no_sorry SerrePositivity.DerivedCompletion.restrictedTorAlgebra_isModuleComplete_of_finite
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebra_isModuleComplete_of_finite
assert_no_sorry SerrePositivity.DerivedCompletion.torAlgebra_isModuleComplete_restrict_of_finite
#print axioms SerrePositivity.algebraResolutionTorComparison
#print axioms SerrePositivity.algebraResolutionTorComparison_coefficient_scalar
#print axioms SerrePositivity.torAlgebraComparison
#print axioms SerrePositivity.torAlgebraComparison_coefficient_scalar
#print axioms SerrePositivity.torAlgebraComparison_scalar_eq_zero_iff
#print axioms SerrePositivity.torAlgebraComparison_scalar_zero_iff_forall
#print axioms SerrePositivity.torAlgebraComparison_restricted_annihilator_iff
#print axioms SerrePositivity.DerivedCompletion.torModule_isModuleComplete_of_finite
#print axioms SerrePositivity.DerivedCompletion.restrictedTorAlgebra_isModuleComplete_of_finite
#print axioms SerrePositivity.DerivedCompletion.torAlgebra_isModuleComplete_of_finite
#print axioms SerrePositivity.DerivedCompletion.torAlgebra_isModuleComplete_restrict_of_finite

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
variable {R : Type u} [CommRing R] (C : Type u) [CommRing C] [Algebra R C]

-- Arbitrary test module and coefficient element, including degree zero.
example (M : ModuleCat.{u} R) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c = 0 ↔
      ∀ x : ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M, c • x = 0 :=
  torAlgebraComparison_scalar_zero_iff_forall M i c

-- The coefficient source need not be Noetherian, flat or finite over the base.
example [IsRegularLocalRing R] (M : ModuleCat.{u} R) [Module.Finite R M]
    (B : Type u) [CommRing B] (ψ : B →+* C) (p : ℕ)
    (hC : IsModuleComplete R (p : R) (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) :=
  torAlgebra_isModuleComplete_restrict_of_finite C M B ψ p hC i
