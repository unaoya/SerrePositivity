import SerrePositivity.BhattScholze.PerfectDeltaIteratedTensorH0
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0_self_complete_p
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0_self_complete_d
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_comparison_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_unit_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_base_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_distinguished
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Prism
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Prism_generator
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Prism_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0PrismComparison
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0PrismComparison_bijective
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0_quotient_isIntegralPerfectoid

#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0_self_complete_p
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorH0_self_complete_d
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_isPerfect
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_comparison_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_unit_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_base_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Structure_distinguished
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Prism
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Prism_generator
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0Prism_isPerfect
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0PrismComparison
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0PrismComparison_bijective
#print axioms SerrePositivity.BhattScholze.perfectDeltaIteratedTensorH0_quotient_isIntegralPerfectoid

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)

-- All prism fields and perfectness hold on the actual original H⁰ ring,
-- with the original base scalar as its chosen generator.
example :
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    ∃ P : OrientedPrism p C, P.generator = algebraMap R C d ∧ P.deltaStructure.IsPerfect := by
  exact ⟨perfectDeltaIteratedTensorH0Prism p R S T DR DS DT hR hS hT hRS hRT d hd,
    perfectDeltaIteratedTensorH0Prism_generator p R S T DR DS DT hR hS hT hRS hRT d hd,
    perfectDeltaIteratedTensorH0Prism_isPerfect p R S T DR DS DT hR hS hT hRS hRT d hd⟩

-- The literal quotient of that original H⁰ by its original generator is covered.
example :
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    IsIntegralPerfectoid (C ⧸ Ideal.span {algebraMap R C d}) p :=
  perfectDeltaIteratedTensorH0_quotient_isIntegralPerfectoid p R S T DR DS DT hR hS hT hRS hRT d hd
