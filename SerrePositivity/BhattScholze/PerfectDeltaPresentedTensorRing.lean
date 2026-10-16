module
public import SerrePositivity.BhattScholze.PerfectDeltaCartierTensorAlgEquiv
public import SerrePositivity.BhattScholze.PerfectoidRingEquiv
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorH0RingTransport

/-! # The original completed tensor H⁰ under compatible perfect-delta residue presentations

The comparison is a ring equivalence through the original ordinary tensors and
their actual completion units. It does not require p-regularity of these tensors.
-/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    [IsAdicComplete (Ideal.span {(p : B)}) B]
    [IsAdicComplete (Ideal.span {(p : C)}) C]
    (DA : DeltaStructure p A) (DB : DeltaStructure p B) (DC : DeltaStructure p C)
    (hA : DA.IsPerfect) (hB : DB.IsPerfect) (hC : DC.IsPerfect)
    (hAB : DA.IsDeltaHom DB (algebraMap A B))
    (hAC : DA.IsDeltaHom DC (algebraMap A C)) (d : A) (hd : DA.IsDistinguished d)
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (eR : (A ⧸ Ideal.span {d}) ≃+* R)
    (eS : (B ⧸ Ideal.map (algebraMap A B) (Ideal.span {d})) ≃+* S)
    (eT : (C ⧸ Ideal.map (algebraMap A C) (Ideal.span {d})) ≃+* T)
    (heS : eS.toRingHom.comp
      (algebraMap (A ⧸ Ideal.span {d}) (B ⧸ Ideal.map (algebraMap A B) (Ideal.span {d}))) =
        (algebraMap R S).comp eR.toRingHom)
    (heT : eT.toRingHom.comp
      (algebraMap (A ⧸ Ideal.span {d}) (C ⧸ Ideal.map (algebraMap A C) (Ideal.span {d}))) =
        (algebraMap R T).comp eR.toRingHom)
local notation "AP" => boundedAboveCompletedTensorAlgebra A (p : A) B C
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor A d).obj AP
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (AD).X.obj
local notation "ORIG" => boundedAboveCompletedTensorAlgebra R (p : R) S T

/-- The actual original completed tensor H⁰ is the actual perfect-prism Cartier quotient. -/
def perfectDelta_presentedCompletedTensorH0RingEquiv :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing ORIG
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ORIG).X.obj ≃+*
      H ⧸ Ideal.span {algebraMap A H d} := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := derivedH0CommRing ORIG
  let Q := A ⧸ Ideal.span {d}
  let SQ := B ⧸ Ideal.map (algebraMap A B) (Ideal.span {d})
  let TQ := C ⧸ Ideal.map (algebraMap A C) (Ideal.span {d})
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ
  letI := derivedH0CommRing RES
  letI := derivedH0Algebra RES
  let e := completedTensorH0RingEquivOfPresentations Q p SQ TQ R S T eR eS eT
    (fun x => RingHom.congr_fun heS x) (fun x => RingHom.congr_fun heT x)
  exact e.symm.trans
    (perfectDelta_completedResidueTensorCartierAlgEquiv p A B C DA DB DC
      hA hB hC hAB hAC d hd).toRingEquiv

include hA hB hC hAB hAC hd eR eS eT heS heT in
/-- Perfectoidness of the actual original H⁰ ring follows from the Cartier ring comparison. -/
lemma perfectDelta_presentedCompletedTensorH0_isIntegralPerfectoid :
    letI := derivedH0CommRing ORIG
    IsIntegralPerfectoid
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ORIG).X.obj) p := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := derivedH0CommRing ORIG
  exact isIntegralPerfectoid_of_ringEquiv p
    (perfectDelta_presentedCompletedTensorH0RingEquiv
      (p := p) (A := A) (B := B) (C := C) (DA := DA) (DB := DB) (DC := DC)
      (hA := hA) (hB := hB) (hC := hC) (hAB := hAB) (hAC := hAC) (d := d) (hd := hd)
      (R := R) (S := S) (T := T) (eR := eR) (eS := eS) (eT := eT)
      (heS := heS) (heT := heT)).symm
    (perfectDeltaIteratedTensorH0_quotient_isIntegralPerfectoid p A B C DA DB DC
      hA hB hC hAB hAC d hd)

end SerrePositivity.BhattScholze
