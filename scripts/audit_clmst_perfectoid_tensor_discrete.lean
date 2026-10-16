import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorZero
import SerrePositivity.BhattScholze.FontaineCompletedTensorDiscrete
import SerrePositivity.BhattScholze.PerfectoidCompletedTensorDiscrete
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.derivedCompletion_isZero_of_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.boundedAboveDerivedSingle_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_of_left_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensor_isZero_of_right_isZero
assert_no_sorry SerrePositivity.BhattScholze.fontaine_completedTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedTensor_pure

#print axioms SerrePositivity.DerivedCompletion.derivedCompletion_isZero_of_isZero
#print axioms SerrePositivity.DerivedCompletion.boundedAboveDerivedSingle_isZero
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_of_left_isZero
#print axioms SerrePositivity.DerivedCompletion.completedTensor_isZero_of_right_isZero
#print axioms SerrePositivity.BhattScholze.fontaine_completedTensor_pure
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedTensor_pure

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard

theorem audit_actual_perfectoid_diagonal_tensor (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) :
    (boundedAboveCompletedTensorAlgebra R (p : R) R R).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) R R).X.obj.IsLE 0 :=
  integralPerfectoid_completedTensor_pure p R R R hR hR hR

theorem audit_actual_perfectoid_zero_factor (p : ℕ) [Fact p.Prime]
    (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) :
    let T := R ⧸ (⊤ : Ideal R)
    (boundedAboveCompletedTensorAlgebra R (p : R) R T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) R T).X.obj.IsLE 0 := by
  exact integralPerfectoid_completedTensor_pure p R R (R ⧸ (⊤ : Ideal R))
    hR hR (Or.inl inferInstance)

assert_no_sorry audit_actual_perfectoid_diagonal_tensor
assert_no_sorry audit_actual_perfectoid_zero_factor
#print axioms audit_actual_perfectoid_diagonal_tensor
#print axioms audit_actual_perfectoid_zero_factor
