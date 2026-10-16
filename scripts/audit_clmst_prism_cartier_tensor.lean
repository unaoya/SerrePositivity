import SerrePositivity.BhattScholze.PerfectPrismCartierTensorComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_completedResidueTensorFactorIso
assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_completedResidueTensorCartierAlgEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_completedResidueTensor_pure

#print axioms SerrePositivity.BhattScholze.perfectPrism_completedResidueTensorFactorIso
#print axioms SerrePositivity.BhattScholze.perfectPrism_completedResidueTensorCartierAlgEquiv
#print axioms SerrePositivity.BhattScholze.perfectPrism_completedResidueTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectPrism_completedResidueTensor_isIntegralPerfectoid
#print axioms SerrePositivity.BhattScholze.perfectPrism_completedResidueTensor_isIntegralPerfectoid

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra

-- Actual own-ideal residues, original prism quotient actions, no separate Tor/purity hypotheses.
theorem audit_actual_prism_cartier_unit_and_purity
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect)
    (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let Q := R ⧸ PR.ideal
    letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
    letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
    let AD := (boundedAboveCompletionCommMonFunctor R PR.generator).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q (C ⧸ Ideal.span {algebraMap R C PR.generator}) :=
      principalAdicQuotientAlgebra PR.generator C
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (RES.X.obj.IsGE 0 ∧ RES.X.obj.IsLE 0) ∧
      IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj RES.X.obj) p ∧
      perfectPrism_completedResidueTensorCartierAlgEquiv PR PS PT hR hS hT fS fT hfS hfT 1 = 1 := by
  let Q := R ⧸ PR.ideal
  letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
  letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
  let AD := (boundedAboveCompletionCommMonFunctor R PR.generator).obj
    (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q (C ⧸ Ideal.span {algebraMap R C PR.generator}) :=
    principalAdicQuotientAlgebra PR.generator C
  letI := derivedH0CommRing RES
  letI := derivedH0Algebra RES
  refine ⟨perfectPrism_completedResidueTensor_pure PR PS PT hR hS hT fS fT hfS hfT,
    perfectPrism_completedResidueTensor_isIntegralPerfectoid PR PS PT hR hS hT fS fT hfS hfT, ?_⟩
  exact map_one (perfectPrism_completedResidueTensorCartierAlgEquiv PR PS PT hR hS hT fS fT hfS hfT)

assert_no_sorry audit_actual_prism_cartier_unit_and_purity
#print axioms audit_actual_prism_cartier_unit_and_purity
