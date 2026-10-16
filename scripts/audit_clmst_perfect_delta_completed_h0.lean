import SerrePositivity.BhattScholze.PerfectDeltaCompletedTensorH0
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.comapEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.completedTensorH0LeftRingHom
assert_no_sorry SerrePositivity.BhattScholze.completedTensorH0RightRingHom
assert_no_sorry SerrePositivity.BhattScholze.completedTensorH0LeftRingHom_comparison
assert_no_sorry SerrePositivity.BhattScholze.completedTensorH0RightRingHom_comparison
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_includeLeft_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_includeRight_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_base_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensor_discrete_perfect
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_distinguished
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_distinguished_regular

#print axioms SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.comapEquiv
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_isPerfect
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom
#print axioms SerrePositivity.BhattScholze.completedTensorH0LeftRingHom
#print axioms SerrePositivity.BhattScholze.completedTensorH0RightRingHom
#print axioms SerrePositivity.BhattScholze.completedTensorH0LeftRingHom_comparison
#print axioms SerrePositivity.BhattScholze.completedTensorH0RightRingHom_comparison
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_includeLeft_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_includeRight_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_base_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensor_discrete_perfect
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_distinguished
#print axioms SerrePositivity.BhattScholze.perfectDeltaCompletedTensorH0Structure_distinguished_regular

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))

-- The original derived tensor object and original H0 ring occur in the conclusion.
example :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 ∧
        (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect :=
  perfectDeltaCompletedTensor_discrete_perfect p R S T DR DS DT hR hS hT hRS hRT

example :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DS.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0LeftRingHom p R S T) :=
  perfectDeltaCompletedTensorH0Structure_includeLeft_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT

example :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DR.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap R ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj)) :=
  perfectDeltaCompletedTensorH0Structure_base_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT

example (d : R) (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj =>
        algebraMap R ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) d * x) :=
  perfectDeltaCompletedTensorH0Structure_distinguished_regular p R S T DR DS DT
    hR hS hT hRS hRT d hd
