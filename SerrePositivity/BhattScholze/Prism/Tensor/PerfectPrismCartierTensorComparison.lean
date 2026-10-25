module
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismResidueFactor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectDeltaCartierTensorAlgEquiv
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidRingEquiv
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAlgebraCongruence

/-! # Cartier tensor comparison using each perfect prism's own residue ring -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Compare the original completed tensor with the actual prism residue factors as algebras. -/
def perfectPrism_completedResidueTensorFactorIso
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect)
    (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let Q := R ⧸ PR.ideal
    letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
    letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
    boundedAboveCompletedTensorAlgebra Q (p : Q)
        (S ⧸ Ideal.map (algebraMap R S) PR.ideal)
        (T ⧸ Ideal.map (algebraMap R T) PR.ideal) ≅
      boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal) := by
  let Q := R ⧸ PR.ideal
  letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
  letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
  exact boundedAboveCompletedTensorAlgebraIso (p : Q)
    (perfectPrismResidueFactorAlgEquiv PR PS hR hS fS hfS)
    (perfectPrismResidueFactorAlgEquiv PR PT hR hT fT hfT)

/-- Each prism's own Cartier residue tensor has the original Cartier quotient algebra as H⁰. -/
def perfectPrism_completedResidueTensorCartierAlgEquiv
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect)
    (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let d := PR.generator
    let Q := R ⧸ PR.ideal
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
    letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
    letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q (C ⧸ Ideal.span {algebraMap R C d}) := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj RES.X.obj ≃ₐ[Q]
      C ⧸ Ideal.span {algebraMap R C d} := by
  let Q := R ⧸ PR.ideal
  letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
  letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
  letI := PR.isAdicComplete_p_of_perfect hR
  letI := PS.isAdicComplete_p_of_perfect hS
  letI := PT.isAdicComplete_p_of_perfect hT
  let AD := (boundedAboveCompletionCommMonFunctor R PR.generator).obj
    (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let C := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD.X.obj
  let OLD := boundedAboveCompletedTensorAlgebra Q (p : Q)
    (S ⧸ Ideal.map (algebraMap R S) PR.ideal) (T ⧸ Ideal.map (algebraMap R T) PR.ideal)
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q (C ⧸ Ideal.span {algebraMap R C PR.generator}) :=
    principalAdicQuotientAlgebra PR.generator C
  letI := derivedH0CommRing OLD
  letI := derivedH0Algebra OLD
  letI := derivedH0CommRing RES
  letI := derivedH0Algebra RES
  have hRS : PR.deltaStructure.IsDeltaHom PS.deltaStructure (algebraMap R S) := by
    simpa only [hfS] using fS.map_delta
  have hRT : PR.deltaStructure.IsDeltaHom PT.deltaStructure (algebraMap R T) := by
    simpa only [hfT] using fT.map_delta
  let e := perfectPrism_completedResidueTensorFactorIso PR PS PT hR hS hT fS fT hfS hfT
  exact (derivedH0AlgEquivOfIsoUnderlying e.hom inferInstance).symm.trans
    (perfectDelta_completedResidueTensorCartierAlgEquiv p R S T PR.deltaStructure
      PS.deltaStructure PT.deltaStructure hR hS hT hRS hRT PR.generator
      (PR.isDistinguished_of_perfect hR))

/-- The completed tensor of the actual prism residues is concentrated in degree zero. -/
lemma perfectPrism_completedResidueTensor_pure
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect)
    (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let Q := R ⧸ PR.ideal
    letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
    letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
    RES.X.obj.IsGE 0 ∧ RES.X.obj.IsLE 0 := by
  let Q := R ⧸ PR.ideal
  letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
  letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
  letI := PR.isAdicComplete_p_of_perfect hR
  letI := PS.isAdicComplete_p_of_perfect hS
  letI := PT.isAdicComplete_p_of_perfect hT
  have hRS : PR.deltaStructure.IsDeltaHom PS.deltaStructure (algebraMap R S) := by
    simpa only [hfS] using fS.map_delta
  have hRT : PR.deltaStructure.IsDeltaHom PT.deltaStructure (algebraMap R T) := by
    simpa only [hfT] using fT.map_delta
  have h := perfectDelta_completedResidueTensor_pure p R S T PR.deltaStructure
    PS.deltaStructure PT.deltaStructure hR hS hT hRS hRT PR.generator
    (PR.isDistinguished_of_perfect hR)
  let OLD := boundedAboveCompletedTensorAlgebra Q (p : Q)
    (S ⧸ Ideal.map (algebraMap R S) PR.ideal) (T ⧸ Ideal.map (algebraMap R T) PR.ideal)
  letI : OLD.X.obj.IsGE 0 := h.1
  letI : OLD.X.obj.IsLE 0 := h.2
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
  let e : OLD.X.obj ≅ RES.X.obj := (DerivedCategory.Minus.ι).mapIso ((CommMon.forget _).mapIso
    (perfectPrism_completedResidueTensorFactorIso PR PS PT hR hS hT fS fT hfS hfT))
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e 0,
    DerivedCategory.TStructure.t.isLE_of_iso e 0⟩

/-- The H⁰ ring of the actual residue tensor is integral perfectoid with its original product. -/
lemma perfectPrism_completedResidueTensor_isIntegralPerfectoid
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect)
    (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let Q := R ⧸ PR.ideal
    letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
    letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (S ⧸ PS.ideal) (T ⧸ PT.ideal)
    letI := derivedH0CommRing RES
    IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj RES.X.obj) p := by
  let Q := R ⧸ PR.ideal
  letI : Algebra Q (S ⧸ PS.ideal) := fS.quotientMap.toAlgebra
  letI : Algebra Q (T ⧸ PT.ideal) := fT.quotientMap.toAlgebra
  letI := PR.isAdicComplete_p_of_perfect hR
  letI := PS.isAdicComplete_p_of_perfect hS
  letI := PT.isAdicComplete_p_of_perfect hT
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
  have hRS : PR.deltaStructure.IsDeltaHom PS.deltaStructure (algebraMap R S) := by
    simpa only [hfS] using fS.map_delta
  have hRT : PR.deltaStructure.IsDeltaHom PT.deltaStructure (algebraMap R T) := by
    simpa only [hfT] using fT.map_delta
  exact isIntegralPerfectoid_of_ringEquiv p
    (perfectPrism_completedResidueTensorCartierAlgEquiv
      PR PS PT hR hS hT fS fT hfS hfT).toRingEquiv.symm
    (perfectDeltaIteratedTensorH0_quotient_isIntegralPerfectoid p R S T PR.deltaStructure
      PS.deltaStructure PT.deltaStructure hR hS hT hRS hRT PR.generator
      (PR.isDistinguished_of_perfect hR))

end SerrePositivity.BhattScholze
