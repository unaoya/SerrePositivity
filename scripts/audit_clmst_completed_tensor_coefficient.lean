import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorCoefficient
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.derivedTensorH0AlgEquiv_map_left
assert_no_sorry SerrePositivity.derivedTensorH0_left_coefficient_mul
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0LeftAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0LeftAlgHom_apply
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0LeftAlgebra
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0LeftScalarTower
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0_left_coefficient_mul
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0_left_coefficient_smul
#print axioms SerrePositivity.derivedTensorH0AlgEquiv_map_left
#print axioms SerrePositivity.derivedTensorH0_left_coefficient_mul
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0LeftAlgHom
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0LeftAlgHom_apply
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0LeftAlgebra
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0LeftScalarTower
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0_left_coefficient_mul
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0_left_coefficient_smul

noncomputable section
universe u
open CategoryTheory MonoidalCategory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

theorem audit_completed_tensor_unit_coefficient
    (z : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R (1 : S))))
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))))).hom z = z := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  exact (completedTensorH0_left_coefficient_smul R a S T 1 z).trans (one_smul S z)

theorem audit_completed_tensor_nilpotent_coefficient (s : S) (k : ℕ) (hs : s ^ k = 0)
    (z : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R (s ^ k))))
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))))).hom z = 0 := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  have hz : s ^ k • z = 0 := by rw [hs, zero_smul]
  exact (completedTensorH0_left_coefficient_smul R a S T (s ^ k) z).trans hz

assert_no_sorry audit_completed_tensor_unit_coefficient
assert_no_sorry audit_completed_tensor_nilpotent_coefficient
#print axioms audit_completed_tensor_unit_coefficient
#print axioms audit_completed_tensor_nilpotent_coefficient
