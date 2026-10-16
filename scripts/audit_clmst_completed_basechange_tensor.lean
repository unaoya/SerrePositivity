import SerrePositivity.HomologicalAlgebra.PowerTorsionCompletedBaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.scalarExtensionTorVanishing_of_completelyFlat_powerTorsion
assert_no_sorry SerrePositivity.powerTorsionCompletedBaseChangeTensorIso
assert_no_sorry SerrePositivity.powerTorsionCompletedBaseChangeTensor_annihilated_iff
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_iff_completed_baseChange_tensor_annihilated
#print axioms SerrePositivity.scalarExtensionTorVanishing_of_completelyFlat_powerTorsion
#print axioms SerrePositivity.powerTorsionCompletedBaseChangeTensorIso
#print axioms SerrePositivity.powerTorsionCompletedBaseChangeTensor_annihilated_iff
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_iff_completed_baseChange_tensor_annihilated

noncomputable section
universe u
open CategoryTheory MonoidalCategory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- The original annihilator exponent survives the actual completed-coefficient comparison.
-- Includes arbitrary coefficient algebras, degree zero, and torsion exponent zero.
theorem audit_original_torsion_exponent_completed_baseChange
    {R S C : Type u} [CommRing R] [CommRing S] [CommRing C] [Algebra R C]
    (φ : R →+* S) (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) (i : ℕ) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).obj
      ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))) ⊗
        boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj N)).obj,
      (φ a) ^ k • x = 0 := by
  have hz : torCoefficientScalarEndomorphism C N i (algebraMap R C (a ^ k)) = 0 :=
    (torCoefficientScalar_eq_zero_iff_derivedTensor_annihilated N i (a ^ k)).mpr
      (derivedTensor_homology_annihilated_of_right_annihilates (ModuleCat.of R C) N
        (a ^ k) hN (-(i : ℤ)))
  simpa only [map_pow] using
    (torCoefficientScalar_eq_zero_iff_completed_baseChange_tensor_annihilated
      φ a hS N k hN i (a ^ k)).mp hz

assert_no_sorry audit_original_torsion_exponent_completed_baseChange
#print axioms audit_original_torsion_exponent_completed_baseChange
