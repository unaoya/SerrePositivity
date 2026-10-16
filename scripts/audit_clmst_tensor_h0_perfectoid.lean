import SerrePositivity.BhattScholze.PerfectDeltaPresentedTensorRing
import SerrePositivity.BhattScholze.PerfectoidCompletedTensorDiscrete
import SerrePositivity.CLMST.PerfectoidIdealCompletedMul
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_presentedCompletedTensorH0RingEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_presentedCompletedTensorH0_isIntegralPerfectoid
assert_no_sorry SerrePositivity.BhattScholze.fontaine_completedTensor_pure_and_h0
assert_no_sorry SerrePositivity.BhattScholze.fontaine_completedTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedTensor_pure_and_h0
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.integralPerfectoid_completedTensorH0_isIntegralPerfectoid
#print axioms SerrePositivity.BhattScholze.perfectDelta_presentedCompletedTensorH0RingEquiv
#print axioms SerrePositivity.BhattScholze.perfectDelta_presentedCompletedTensorH0_isIntegralPerfectoid
#print axioms SerrePositivity.BhattScholze.fontaine_completedTensor_pure_and_h0
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedTensor_pure_and_h0
#print axioms SerrePositivity.BhattScholze.integralPerfectoid_completedTensorH0_isIntegralPerfectoid

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.BhattScholze SerrePositivity.CLMST
  SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- The actual H⁰ ring can now serve as a base for the original CLMST ideal constructions.
theorem audit_completedTensorH0_actual_perfectoid_ideal
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    let X := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.X.obj
    letI := derivedH0CommRing X
    let hH := integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR hS hT
    ∀ (g : H) (n : ℕ), IsIdempotentElem ((perfectoidIdeal H p hH g).map
      (Ideal.Quotient.mk (Ideal.span {(p : H) ^ n}))) := by
  dsimp only
  let X := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.X.obj
  letI := derivedH0CommRing X
  let hH := integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR hS hT
  intro g n
  exact perfectoidIdeal_mod_power_idempotent H p hH g n

-- Zero factors stay zero in the actual H⁰ ring and satisfy the same perfectoid theorem.
theorem audit_completedTensorH0_zero_factor
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Subsingleton S]
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p) :
    let X := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.X.obj
    letI := derivedH0CommRing X
    IsIntegralPerfectoid H p ∧ Subsingleton H := by
  constructor
  · exact integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR
      (Or.inl inferInstance) hT
  · exact ModuleCat.isZero_iff_subsingleton.mp
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map_isZero
        (completedTensor_isZero_of_left_isZero R (p : R) (ModuleCat.of R S)
          (ModuleCat.of R T) (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)))

assert_no_sorry audit_completedTensorH0_actual_perfectoid_ideal
assert_no_sorry audit_completedTensorH0_zero_factor
#print axioms audit_completedTensorH0_actual_perfectoid_ideal
#print axioms audit_completedTensorH0_zero_factor
