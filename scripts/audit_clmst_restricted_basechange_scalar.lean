import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeScalar
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.restrictedScalarMultiplication
#print axioms SerrePositivity.restrictedScalarMultiplication
assert_no_sorry SerrePositivity.restrictedScalarMultiplication_algebraMap
#print axioms SerrePositivity.restrictedScalarMultiplication_algebraMap
assert_no_sorry SerrePositivity.extendRestrictTensorIso_scalar
#print axioms SerrePositivity.extendRestrictTensorIso_scalar
assert_no_sorry SerrePositivity.restrictedBaseChangeComplexIso_scalar
#print axioms SerrePositivity.restrictedBaseChangeComplexIso_scalar
assert_no_sorry SerrePositivity.restrictedDerivedBaseChangeModelIso_scalar
#print axioms SerrePositivity.restrictedDerivedBaseChangeModelIso_scalar
assert_no_sorry SerrePositivity.derivedScalarTensorModelIso_first_naturality
#print axioms SerrePositivity.derivedScalarTensorModelIso_first_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeTensorIso_scalar
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeTensorIso_scalar

noncomputable section
universe u
open CategoryTheory MonoidalCategory SerrePositivity
attribute [local instance] HasDerivedCategory.standard

-- The new scalar-factor action agrees with the original base scalar on the actual derived tensor.
theorem audit_scalar_factor_original_base_action
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (r : R) :
    boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ (φ r))) (𝟙 X)) =
      r • 𝟙 (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule φ) ⊗ X) := by
  change (boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ (φ r))) ⊗ₘ
    (𝟙 X) = _
  have hs : boundedAboveDerivedSingleFunctor.map (r • 𝟙 (baseChangeScalarModule φ)) =
      r • 𝟙 (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule φ)) := by
    apply InducedCategory.hom_ext
    change (DerivedCategory.singleFunctor (ModuleCat R) 0).map
      (r • 𝟙 (baseChangeScalarModule φ)) =
        r • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (baseChangeScalarModule φ))
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [restrictedScalarMultiplication_algebraMap, hs, derivedTensorHom_smul_left,
    id_tensorHom_id]

assert_no_sorry audit_scalar_factor_original_base_action
#print axioms audit_scalar_factor_original_base_action

