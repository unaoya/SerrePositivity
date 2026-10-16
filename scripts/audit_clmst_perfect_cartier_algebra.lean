import SerrePositivity.BhattScholze.PerfectDeltaCartierTensorAlgebra
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_iteratedTensorCartier_isAdicComplete
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_iteratedTensorCartier_isModuleComplete
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgHom

#print axioms SerrePositivity.BhattScholze.perfectDelta_iteratedTensorCartier_isAdicComplete
#print axioms SerrePositivity.BhattScholze.perfectDelta_iteratedTensorCartier_isModuleComplete
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgHom

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra

-- Actual perfect prism data supplies every input, including the original Cartier completeness.
example (p : ℕ) [Fact p.Prime] (R S T : Type u)
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
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj RES.X.obj →ₐ[Q]
      C ⧸ Ideal.span {algebraMap R C d} := by
  have hRS : PR.deltaStructure.IsDeltaHom PS.deltaStructure (algebraMap R S) := by
    simpa only [hfS] using fS.map_delta
  have hRT : PR.deltaStructure.IsDeltaHom PT.deltaStructure (algebraMap R T) := by
    simpa only [hfT] using fT.map_delta
  exact perfectDelta_completedResidueTensorCartierAlgHom p R S T PR.deltaStructure
    PS.deltaStructure PT.deltaStructure hR hS hT hRS hRT PR.generator
    (PR.isDistinguished_of_perfect hR)

assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgHom_unit
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgHom_unit_tmul

#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgHom_unit
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierAlgHom_unit_tmul

-- The original source class of 1 maps to 1 after the normalized original completion unit.
example (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d) :
    let Q := R ⧸ Ideal.span {d}
    let SQ := S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
    let TQ := T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    let RX := boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    perfectDelta_completedResidueTensorCartierAlgHom p R S T
        DR DS DT hR hS hT hRS hRT d hd
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q (p : Q) RX)
          ((derivedTensorH0AlgEquiv (R := Q) SQ TQ).symm 1)) = 1 := by
  let Q := R ⧸ Ideal.span {d}
  let SQ := S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
  let TQ := T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
  let AD := (boundedAboveCompletionCommMonFunctor R d).obj
    (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let RX := boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing RES
  let := derivedH0Algebra RES
  dsimp only
  rw [perfectDelta_completedResidueTensorCartierAlgHom_unit,
    AlgEquiv.apply_symm_apply, map_one]
