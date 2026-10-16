import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeH0Coefficient
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.baseChangeScalarNormalizationIso
assert_no_sorry SerrePositivity.DerivedCompletion.baseChangeScalarNormalizationIso_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.completedScalarTensorNormalizationIso
assert_no_sorry SerrePositivity.DerivedCompletion.completedScalarTensorNormalizationIso_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0Iso
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0Iso_smul
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0LinearEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0LinearEquiv_apply
#print axioms SerrePositivity.DerivedCompletion.baseChangeScalarNormalizationIso
#print axioms SerrePositivity.DerivedCompletion.baseChangeScalarNormalizationIso_scalar
#print axioms SerrePositivity.DerivedCompletion.completedScalarTensorNormalizationIso
#print axioms SerrePositivity.DerivedCompletion.completedScalarTensorNormalizationIso_scalar
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0Iso
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0Iso_smul
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0LinearEquiv
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorH0LinearEquiv_apply

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (a : R)

theorem audit_actual_baseChange_H0_scalar_annihilation (s : S) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj, s • x = 0) ↔
    (∀ z : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj, s • z = 0) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  let e := completedBaseChangeTensorH0LinearEquiv R S T a
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [← e.map_smul, h, map_zero]
  · intro h x
    apply e.injective
    rw [e.map_smul, h, map_zero]

assert_no_sorry audit_actual_baseChange_H0_scalar_annihilation
#print axioms audit_actual_baseChange_H0_scalar_annihilation
