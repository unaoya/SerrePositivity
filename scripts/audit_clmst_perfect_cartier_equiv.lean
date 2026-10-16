import SerrePositivity.BhattScholze.PerfectDeltaCartierTensorAlgEquiv
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_cartierTensor_inputs
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgEquiv_toAlgHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgEquiv_toLinearEquiv

#print axioms SerrePositivity.BhattScholze.perfectDelta_cartierTensor_inputs
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgEquiv
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgEquiv_toAlgHom
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgEquiv_toLinearEquiv

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra

-- Actual perfect prisms and their original morphisms supply every input; no extra purity or Tor data.
def audit_actual_perfect_prism_cartier_equiv (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect) (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let d := PR.generator
    let Q := R ⧸ Ideal.span {d}
    let SQ := S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
    let TQ := T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj RES.X.obj ≃ₐ[Q]
      C ⧸ Ideal.span {algebraMap R C d} := by
  let := PR.isAdicComplete_p_of_perfect hR
  let := PS.isAdicComplete_p_of_perfect hS
  let := PT.isAdicComplete_p_of_perfect hT
  have hRS : PR.deltaStructure.IsDeltaHom PS.deltaStructure (algebraMap R S) := by
    simpa only [hfS] using fS.map_delta
  have hRT : PR.deltaStructure.IsDeltaHom PT.deltaStructure (algebraMap R T) := by
    simpa only [hfT] using fT.map_delta
  exact perfectDelta_completedResidueTensorCartierAlgEquiv p R S T PR.deltaStructure
    PS.deltaStructure PT.deltaStructure hR hS hT hRS hRT PR.generator
    (PR.isDistinguished_of_perfect hR)

assert_no_sorry audit_actual_perfect_prism_cartier_equiv
#print axioms audit_actual_perfect_prism_cartier_equiv
