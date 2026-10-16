import SerrePositivity.BhattScholze.PerfectPrismResidueTensorTransport
import SerrePositivity.BhattScholze.PerfectDeltaResidueTensorTransport
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.ringEquivAlgebraRestrictionModuleIso
#print axioms SerrePositivity.ringEquivAlgebraRestrictionModuleIso

assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_presentedCompletedTensorIso
assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_presentedCompletedTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_presentedCompletedTensor_pure_of_ringEquiv

#print axioms SerrePositivity.BhattScholze.perfectPrism_presentedCompletedTensorIso
#print axioms SerrePositivity.BhattScholze.perfectPrism_presentedCompletedTensor_pure
#print axioms SerrePositivity.BhattScholze.perfectPrism_presentedCompletedTensor_pure_of_ringEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_presentedCompletedTensor_pure
#print axioms SerrePositivity.BhattScholze.perfectDelta_presentedCompletedTensor_pure

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra

theorem audit_prism_quotient_diagram_transport
    (p : ℕ) [Fact p.Prime] (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (PA : OrientedPrism p A) (PB : OrientedPrism p B) (PC : OrientedPrism p C)
    (hA : PA.deltaStructure.IsPerfect) (hB : PB.deltaStructure.IsPerfect)
    (hC : PC.deltaStructure.IsPerfect)
    (fB : OrientedPrism.Hom PA PB) (fC : OrientedPrism.Hom PA PC)
    (hfB : fB.toRingHom = algebraMap A B) (hfC : fC.toRingHom = algebraMap A C) :
    let Q := A ⧸ PA.ideal
    letI : Algebra Q (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
    letI : Algebra Q (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (B ⧸ PB.ideal) (C ⧸ PC.ideal)
    RES.X.obj.IsGE 0 ∧ RES.X.obj.IsLE 0 := by
  let Q := A ⧸ PA.ideal
  letI : Algebra Q (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
  letI : Algebra Q (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
  exact perfectPrism_presentedCompletedTensor_pure_of_ringEquiv
    PA PB PC hA hB hC fB fC hfB hfC (RingEquiv.refl Q)
    (RingEquiv.refl (B ⧸ PB.ideal)) (RingEquiv.refl (C ⧸ PC.ideal))
    (by ext x; rfl) (by ext x; rfl)

assert_no_sorry audit_prism_quotient_diagram_transport
#print axioms audit_prism_quotient_diagram_transport
