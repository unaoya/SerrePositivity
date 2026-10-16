module
public import SerrePositivity.BhattScholze.PerfectDeltaResidueTensorTransport
public import SerrePositivity.BhattScholze.PerfectDeltaPresentedTensorRing
public import SerrePositivity.BhattScholze.PerfectoidWittBasePresentation
public import SerrePositivity.BhattScholze.PerfectoidDistinguishedKernel
public import SerrePositivity.CommutativeAlgebra.MappedPrincipalQuotient

/-! # Discreteness and perfectoid H⁰ from the original Fontaine presentations -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra

/-- The original Fontaine morphisms supply all compatible residue presentations for Cartier descent. -/
lemma fontaine_completedTensor_pure_and_h0
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] [Fact (¬ IsUnit (p : T))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hk : RingHom.ker (WittVector.fontaineTheta R p) = Ideal.span {d})
    (hFR : Function.Surjective (fun x : ModP R p => x ^ p))
    (hFS : Function.Surjective (fun x : ModP S p => x ^ p))
    (hFT : Function.Surjective (fun x : ModP T p => x ^ p))
    (hkerS : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (hkerT : (RingHom.ker (WittVector.fontaineTheta T p)).IsPrincipal) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    ((boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0) ∧
      IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) p := by
  let kR := PreTilt R p
  let kS := PreTilt S p
  let kT := PreTilt T p
  letI : Algebra kR kS := (Perfection.map p (modPMap p (algebraMap R S))).toAlgebra
  letI : Algebra kR kT := (Perfection.map p (modPMap p (algebraMap R T))).toAlgebra
  let A := WittVector p kR
  let B := WittVector p kS
  let C := WittVector p kT
  letI : Algebra A B := (WittVector.map (algebraMap kR kS)).toAlgebra
  letI : Algebra A C := (WittVector.map (algebraMap kR kT)).toAlgebra
  have hzero : WittVector.fontaineTheta R p d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  let eR : (A ⧸ Ideal.span {d}) ≃+* R :=
    (Ideal.quotEquivOfEq hk.symm).trans
      (RingHom.quotientKerEquivOfSurjective (fun x => surjective_fontaineTheta hFR x))
  let eS0 := fontaineBaseWittQuotientEquiv p (algebraMap R S) d hd hzero hFS hkerS
  let eT0 := fontaineBaseWittQuotientEquiv p (algebraMap R T) d hd hzero hFT hkerT
  let eS : (B ⧸ Ideal.map (algebraMap A B) (Ideal.span {d})) ≃+* S :=
    (mappedPrincipalQuotientAlgEquiv A d B).toRingEquiv.trans eS0
  let eT : (C ⧸ Ideal.map (algebraMap A C) (Ideal.span {d})) ≃+* T :=
    (mappedPrincipalQuotientAlgEquiv A d C).toRingEquiv.trans eT0
  have heR (a : A) : eR (Ideal.Quotient.mk (Ideal.span {d}) a) =
      WittVector.fontaineTheta R p a := by
    change RingHom.quotientKerEquivOfSurjective
      (fun x => surjective_fontaineTheta hFR x)
      (Ideal.quotEquivOfEq hk.symm (Ideal.Quotient.mk (Ideal.span {d}) a)) = _
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hs0 (b : B) : eS0 (Ideal.Quotient.mk (Ideal.span {algebraMap A B d}) b) =
      WittVector.fontaineTheta S p b := by
    exact RingHom.congr_fun
      (fontaineBaseWittQuotientEquiv_comp_mk p (algebraMap R S) d hd hzero hFS hkerS) b
  have ht0 (c : C) : eT0 (Ideal.Quotient.mk (Ideal.span {algebraMap A C d}) c) =
      WittVector.fontaineTheta T p c := by
    exact RingHom.congr_fun
      (fontaineBaseWittQuotientEquiv_comp_mk p (algebraMap R T) d hd hzero hFT hkerT) c
  have heS : eS.toRingHom.comp
      (algebraMap (A ⧸ Ideal.span {d}) (B ⧸ Ideal.map (algebraMap A B) (Ideal.span {d}))) =
        (algebraMap R S).comp eR.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change eS0 (mappedPrincipalQuotientAlgEquiv A d B
      (Ideal.Quotient.mk _ (algebraMap A B a))) =
      algebraMap R S (eR (Ideal.Quotient.mk _ a))
    rw [mappedPrincipalQuotientAlgEquiv_mk, hs0, heR]
    change WittVector.fontaineTheta S p
        (WittVector.map (Perfection.map p (modPMap p (algebraMap R S))) a) =
      algebraMap R S (WittVector.fontaineTheta R p a)
    exact RingHom.congr_fun (fontaineTheta_natural p (algebraMap R S)) a
  have heT : eT.toRingHom.comp
      (algebraMap (A ⧸ Ideal.span {d}) (C ⧸ Ideal.map (algebraMap A C) (Ideal.span {d}))) =
        (algebraMap R T).comp eR.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change eT0 (mappedPrincipalQuotientAlgEquiv A d C
      (Ideal.Quotient.mk _ (algebraMap A C a))) =
      algebraMap R T (eR (Ideal.Quotient.mk _ a))
    rw [mappedPrincipalQuotientAlgEquiv_mk, ht0, heR]
    change WittVector.fontaineTheta T p
        (WittVector.map (Perfection.map p (modPMap p (algebraMap R T))) a) =
      algebraMap R T (WittVector.fontaineTheta R p a)
    exact RingHom.congr_fun (fontaineTheta_natural p (algebraMap R T)) a
  constructor
  · exact perfectDelta_presentedCompletedTensor_pure p A B C
      (wittDeltaStructure p kR) (wittDeltaStructure p kS) (wittDeltaStructure p kT)
      (wittDeltaStructure_isPerfect p kR) (wittDeltaStructure_isPerfect p kS)
      (wittDeltaStructure_isPerfect p kT)
      (wittDeltaStructure_map_isDeltaHom p kR (algebraMap kR kS))
      (wittDeltaStructure_map_isDeltaHom p kR (algebraMap kR kT))
      d hd R S T eR eS eT heS heT
  · exact perfectDelta_presentedCompletedTensorH0_isIntegralPerfectoid
      (p := p) (A := A) (B := B) (C := C)
      (DA := wittDeltaStructure p kR) (DB := wittDeltaStructure p kS)
      (DC := wittDeltaStructure p kT)
      (hA := wittDeltaStructure_isPerfect p kR) (hB := wittDeltaStructure_isPerfect p kS)
      (hC := wittDeltaStructure_isPerfect p kT)
      (hAB := wittDeltaStructure_map_isDeltaHom p kR (algebraMap kR kS))
      (hAC := wittDeltaStructure_map_isDeltaHom p kR (algebraMap kR kT))
      (d := d) (hd := hd) (R := R) (S := S) (T := T)
      (eR := eR) (eS := eS) (eT := eT) (heS := heS) (heT := heT)

/-- The original public discreteness statement is retained. -/
lemma fontaine_completedTensor_pure
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] [Fact (¬ IsUnit (p : T))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hk : RingHom.ker (WittVector.fontaineTheta R p) = Ideal.span {d})
    (hFR : Function.Surjective (fun x : ModP R p => x ^ p))
    (hFS : Function.Surjective (fun x : ModP S p => x ^ p))
    (hFT : Function.Surjective (fun x : ModP T p => x ^ p))
    (hkerS : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (hkerT : (RingHom.ker (WittVector.fontaineTheta T p)).IsPrincipal) :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 := by
  exact (fontaine_completedTensor_pure_and_h0 p R S T d hd hk hFR hFS hFT hkerS hkerT).1


end SerrePositivity.BhattScholze
