import SerrePositivity.BhattScholze.PerfectDeltaIteratedTensorDiscrete
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.completedUnitAlgebra_pure_of_regular
assert_no_sorry SerrePositivity.DerivedCompletion.completedAlgebra_pure_of_regular
assert_no_sorry SerrePositivity.DerivedCompletion.derivedAlgebra_completion_pure_of_h0_regular
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_iteratedTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_iteratedTensor_discrete_perfect

#print axioms SerrePositivity.DerivedCompletion.completedUnitAlgebra_pure_of_regular
#print axioms SerrePositivity.DerivedCompletion.completedAlgebra_pure_of_regular
#print axioms SerrePositivity.DerivedCompletion.derivedAlgebra_completion_pure_of_h0_regular
#print axioms SerrePositivity.BhattScholze.perfectDelta_iteratedTensor_pure
#print axioms SerrePositivity.BhattScholze.perfectDelta_iteratedTensor_discrete_perfect

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard

-- No nonzero or nonunit hypothesis is imposed on the regular scalar or its base ring.
example (R : Type u) [CommRing R] :
    (completedUnitAlgebra R 1).X.obj.IsGE 0 ∧
      (completedUnitAlgebra R 1).X.obj.IsLE 0 :=
  completedUnitAlgebra_pure_of_regular R 1 (by intro x y h; simpa only [one_smul] using h)

-- The actual iterated tensor object, not just its H⁰, is covered.
example (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d) :
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing AD
    AD.X.obj.IsGE 0 ∧ AD.X.obj.IsLE 0 ∧
      (perfectDeltaIteratedTensorH0Prism p R S T
        DR DS DT hR hS hT hRS hRT d hd).deltaStructure.IsPerfect :=
  perfectDelta_iteratedTensor_discrete_perfect p R S T DR DS DT hR hS hT hRS hRT d hd
