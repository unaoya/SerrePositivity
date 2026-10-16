import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorH0RingTransport
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletion_isModuleComplete_unit
#print axioms SerrePositivity.DerivedCompletion.principalCompletion_isModuleComplete_unit
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletion_isModuleComplete_comp
#print axioms SerrePositivity.DerivedCompletion.principalCompletion_isModuleComplete_comp
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionMap
#print axioms SerrePositivity.DerivedCompletion.principalCompletionMap
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionMap_comp
#print axioms SerrePositivity.DerivedCompletion.principalCompletionMap_comp
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionRingEquiv
#print axioms SerrePositivity.DerivedCompletion.principalCompletionRingEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionRingEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.principalCompletionRingEquiv_unit
assert_no_sorry SerrePositivity.tensorMapOfCompatibleBase
#print axioms SerrePositivity.tensorMapOfCompatibleBase
assert_no_sorry SerrePositivity.tensorMapOfCompatibleBase_tmul
#print axioms SerrePositivity.tensorMapOfCompatibleBase_tmul
assert_no_sorry SerrePositivity.tensorRingEquivOfCompatibleBase
#print axioms SerrePositivity.tensorRingEquivOfCompatibleBase
assert_no_sorry SerrePositivity.tensorRingEquivOfCompatibleBase_tmul
#print axioms SerrePositivity.tensorRingEquivOfCompatibleBase_tmul
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0PrincipalRingEquiv
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0PrincipalRingEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0PrincipalRingEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0PrincipalRingEquiv_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0RingEquivOfTensorRingEquiv
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0RingEquivOfTensorRingEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0RingEquivOfTensorRingEquiv_unit
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0RingEquivOfTensorRingEquiv_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completedTensorH0RingEquivOfPresentations
#print axioms SerrePositivity.DerivedCompletion.completedTensorH0RingEquivOfPresentations

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

-- Scalar zero forces a nonregular boundary case; both original completion units are retained.
theorem audit_zero_scalar_completed_tensor_swap
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) T S)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) T S)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R ((0 : ℕ) : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R ((0 : ℕ) : R) T S)
    ∃ f : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          (boundedAboveCompletedTensorAlgebra R ((0 : ℕ) : R) S T).X.obj ≃+*
        (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          (boundedAboveCompletedTensorAlgebra R ((0 : ℕ) : R) T S).X.obj,
      ∀ x, f (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R ((0 : ℕ) : R)
          (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
        derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R ((0 : ℕ) : R)
          (boundedAboveDerivedTensorAlgebra (R := R) T S))
          ((derivedTensorH0AlgEquiv T S).symm
            (Algebra.TensorProduct.comm R S T (derivedTensorH0AlgEquiv S T x))) := by
  refine ⟨completedTensorH0RingEquivOfTensorRingEquiv R 0 S T R T S
    (Algebra.TensorProduct.comm R S T).toRingEquiv, ?_⟩
  exact completedTensorH0RingEquivOfTensorRingEquiv_unit R 0 S T R T S _

-- Both the base ring and both factors change; no flatness of S over R is available.
theorem audit_completed_tensor_actual_change_of_base
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S R)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra S (p : S) S S)
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S R).X.obj ≃+*
      (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
        (boundedAboveCompletedTensorAlgebra S (p : S) S S).X.obj) := by
  refine ⟨completedTensorH0RingEquivOfTensorRingEquiv R p S R S S S
    ((Algebra.TensorProduct.rid R R S).toRingEquiv.trans
      (Algebra.TensorProduct.lid S S).toRingEquiv.symm)⟩

assert_no_sorry audit_zero_scalar_completed_tensor_swap
assert_no_sorry audit_completed_tensor_actual_change_of_base
#print axioms audit_zero_scalar_completed_tensor_swap
#print axioms audit_completed_tensor_actual_change_of_base

