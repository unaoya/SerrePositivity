module
public import SerrePositivity.BhattScholze.PerfectDeltaCartierTensorComparison
public import SerrePositivity.HomologicalAlgebra.RingEquivDerivedTensor

/-! # Residue presentations of perfect delta rings and the original completed tensor -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra

/-- Transport the Cartier discreteness theorem through compatible residue presentations.
Only p-completeness of the delta rings is required; their d-completeness is not assumed. -/
lemma perfectDelta_presentedCompletedTensor_pure
    (p : ℕ) [Fact p.Prime] (A B C : Type u)
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
        (algebraMap R T).comp eR.toRingHom) :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 := by
  let Q := A ⧸ Ideal.span {d}
  let SQ := B ⧸ Ideal.map (algebraMap A B) (Ideal.span {d})
  let TQ := C ⧸ Ideal.map (algebraMap A C) (Ideal.span {d})
  let ORIG := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ
  let RX := (boundedAboveDerivedCompletionFunctor Q (p : Q)).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj
        ((ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R S)),
        boundedAboveDerivedSingleFunctor.obj
          ((ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R T))))
  let c : (boundedAboveDerivedRestrictScalars eR.toRingHom).obj ORIG.X ≅ RX := by
    have h := completedTensorModulesRingEquivRestrictionIso eR (p : Q)
      (ModuleCat.of R S) (ModuleCat.of R T)
    rw [map_natCast] at h
    exact h
  let eSQ := ringEquivAlgebraRestrictionModuleIso eR eS heS
  let eTQ := ringEquivAlgebraRestrictionModuleIso eR eT heT
  let e0 : (boundedAboveDerivedRestrictScalars eR.toRingHom).obj ORIG.X ≅ RES.X :=
    c ≪≫ (boundedAboveDerivedCompletionFunctor Q (p : Q)).mapIso
      (boundedAboveDerivedTensor.mapIso (Iso.prod
        (boundedAboveDerivedSingleFunctor.mapIso eSQ)
        (boundedAboveDerivedSingleFunctor.mapIso eTQ)))
  have hp := perfectDelta_completedResidueTensor_pure p A B C DA DB DC
    hA hB hC hAB hAC d hd
  letI : RES.X.obj.IsGE 0 := hp.1
  letI : RES.X.obj.IsLE 0 := hp.2
  let e : ((boundedAboveDerivedRestrictScalars eR.toRingHom).obj ORIG.X).obj ≅ RES.X.obj :=
    DerivedCategory.Minus.ι.mapIso e0
  have hlo := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have hhi := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  exact ⟨(derivedRestrictScalars_isGE_iff eR.toRingHom ORIG.X.obj 0).mp hlo,
    (derivedRestrictScalars_isLE_iff eR.toRingHom ORIG.X.obj 0).mp hhi⟩

end SerrePositivity.BhattScholze
