import SerrePositivity.HomologicalAlgebra.TorCoefficientPowerTorsionDescent
import SerrePositivity.HomologicalAlgebra.TorFiniteFreeComparisonAnnihilator
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.derivedTensor_scalar_id_eq_zero_of_right_annihilates
assert_no_sorry SerrePositivity.derivedTensor_homology_annihilated_of_right_annihilates
assert_no_sorry SerrePositivity.torCoefficientScalar_algebraMap_eq_smul_id
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_iff_derivedTensor_annihilated
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange

#print axioms SerrePositivity.derivedTensor_scalar_id_eq_zero_of_right_annihilates
#print axioms SerrePositivity.derivedTensor_homology_annihilated_of_right_annihilates
#print axioms SerrePositivity.torCoefficientScalar_algebraMap_eq_smul_id
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_iff_derivedTensor_annihilated
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange

noncomputable section
universe u
open CategoryTheory SerrePositivity
attribute [local instance] HasDerivedCategory.standard

-- The entire original tensor and the same test exponent are used; degree zero is included.
theorem audit_original_torsion_scalar_after_actual_baseChange
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C] [Algebra R C]
    (φ : R →+* S) (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) (i : ℕ) :
    let X := boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C), boundedAboveDerivedSingleFunctor.obj N)
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).obj
      ((boundedAboveDerivedBaseChange φ).obj X).obj, φ (a ^ k) • x = 0 := by
  exact (torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange φ a hS N k hN i (a ^ k)).mp
    (torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i (a ^ k) hN)

assert_no_sorry audit_original_torsion_scalar_after_actual_baseChange
#print axioms audit_original_torsion_scalar_after_actual_baseChange
