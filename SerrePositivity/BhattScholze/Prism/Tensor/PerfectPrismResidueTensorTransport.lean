module
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismCartierTensorComparison
public import SerrePositivity.HomologicalAlgebra.RingEquivDerivedTensor

/-! # Transport the actual perfect-prism residue tensor to presented coefficient rings -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime]
    {A B C R S T : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

/-- Use a base residue presentation and the original restricted coefficient modules.
No flatness or additional purity hypotheses are required. -/
def perfectPrism_presentedCompletedTensorIso
    (PA : OrientedPrism p A) (PB : OrientedPrism p B) (PC : OrientedPrism p C)
    (hA : PA.deltaStructure.IsPerfect) (hB : PB.deltaStructure.IsPerfect)
    (hC : PC.deltaStructure.IsPerfect)
    (fB : OrientedPrism.Hom PA PB) (fC : OrientedPrism.Hom PA PC)
    (hfB : fB.toRingHom = algebraMap A B) (hfC : fC.toRingHom = algebraMap A C)
    (eR : (A ⧸ PA.ideal) ≃+* R)
    (eS : letI : Algebra (A ⧸ PA.ideal) (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
      (ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R S) ≅
        ModuleCat.of (A ⧸ PA.ideal) (B ⧸ PB.ideal))
    (eT : letI : Algebra (A ⧸ PA.ideal) (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
      (ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R T) ≅
        ModuleCat.of (A ⧸ PA.ideal) (C ⧸ PC.ideal)) :
    let Q := A ⧸ PA.ideal
    letI : Algebra Q (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
    letI : Algebra Q (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
    (boundedAboveDerivedRestrictScalars eR.toRingHom).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X ≅
      (boundedAboveCompletedTensorAlgebra Q (p : Q) (B ⧸ PB.ideal) (C ⧸ PC.ideal)).X := by
  let Q := A ⧸ PA.ideal
  letI : Algebra Q (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
  letI : Algebra Q (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
  let RX := (boundedAboveDerivedCompletionFunctor Q (p : Q)).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj
        ((ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R S)),
        boundedAboveDerivedSingleFunctor.obj
          ((ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R T))))
  let e0 : (boundedAboveDerivedRestrictScalars eR.toRingHom).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X ≅ RX := by
    have h := completedTensorModulesRingEquivRestrictionIso eR (p : Q)
      (ModuleCat.of R S) (ModuleCat.of R T)
    rw [map_natCast] at h
    exact h
  exact e0 ≪≫ (boundedAboveDerivedCompletionFunctor Q (p : Q)).mapIso
    (boundedAboveDerivedTensor.mapIso (Iso.prod
      (boundedAboveDerivedSingleFunctor.mapIso eS)
      (boundedAboveDerivedSingleFunctor.mapIso eT)))

/-- The original completed tensor is discrete for coefficients presented by perfect prisms. -/
lemma perfectPrism_presentedCompletedTensor_pure
    (PA : OrientedPrism p A) (PB : OrientedPrism p B) (PC : OrientedPrism p C)
    (hA : PA.deltaStructure.IsPerfect) (hB : PB.deltaStructure.IsPerfect)
    (hC : PC.deltaStructure.IsPerfect)
    (fB : OrientedPrism.Hom PA PB) (fC : OrientedPrism.Hom PA PC)
    (hfB : fB.toRingHom = algebraMap A B) (hfC : fC.toRingHom = algebraMap A C)
    (eR : (A ⧸ PA.ideal) ≃+* R)
    (eS : letI : Algebra (A ⧸ PA.ideal) (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
      (ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R S) ≅
        ModuleCat.of (A ⧸ PA.ideal) (B ⧸ PB.ideal))
    (eT : letI : Algebra (A ⧸ PA.ideal) (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
      (ModuleCat.restrictScalars eR.toRingHom).obj (ModuleCat.of R T) ≅
        ModuleCat.of (A ⧸ PA.ideal) (C ⧸ PC.ideal)) :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 := by
  let Q := A ⧸ PA.ideal
  letI : Algebra Q (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
  letI : Algebra Q (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
  let ORIG := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) (B ⧸ PB.ideal) (C ⧸ PC.ideal)
  have hp := perfectPrism_completedResidueTensor_pure PA PB PC hA hB hC fB fC hfB hfC
  letI : RES.X.obj.IsGE 0 := hp.1
  letI : RES.X.obj.IsLE 0 := hp.2
  let e0 : ((boundedAboveDerivedRestrictScalars eR.toRingHom).obj ORIG.X).obj ≅ RES.X.obj :=
    DerivedCategory.Minus.ι.mapIso
      (perfectPrism_presentedCompletedTensorIso PA PB PC hA hB hC fB fC hfB hfC eR eS eT)
  have hlo := DerivedCategory.TStructure.t.isGE_of_iso e0.symm 0
  have hhi := DerivedCategory.TStructure.t.isLE_of_iso e0.symm 0
  exact ⟨(derivedRestrictScalars_isGE_iff eR.toRingHom ORIG.X.obj 0).mp hlo,
    (derivedRestrictScalars_isLE_iff eR.toRingHom ORIG.X.obj 0).mp hhi⟩

/-- Supply the coefficient modules from ring presentations and the original quotient-map diagram. -/
lemma perfectPrism_presentedCompletedTensor_pure_of_ringEquiv
    (PA : OrientedPrism p A) (PB : OrientedPrism p B) (PC : OrientedPrism p C)
    (hA : PA.deltaStructure.IsPerfect) (hB : PB.deltaStructure.IsPerfect)
    (hC : PC.deltaStructure.IsPerfect)
    (fB : OrientedPrism.Hom PA PB) (fC : OrientedPrism.Hom PA PC)
    (hfB : fB.toRingHom = algebraMap A B) (hfC : fC.toRingHom = algebraMap A C)
    (eR : (A ⧸ PA.ideal) ≃+* R)
    (eS : (B ⧸ PB.ideal) ≃+* S) (eT : (C ⧸ PC.ideal) ≃+* T)
    (heS : eS.toRingHom.comp fB.quotientMap = (algebraMap R S).comp eR.toRingHom)
    (heT : eT.toRingHom.comp fC.quotientMap = (algebraMap R T).comp eR.toRingHom) :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 := by
  letI : Algebra (A ⧸ PA.ideal) (B ⧸ PB.ideal) := fB.quotientMap.toAlgebra
  letI : Algebra (A ⧸ PA.ideal) (C ⧸ PC.ideal) := fC.quotientMap.toAlgebra
  exact perfectPrism_presentedCompletedTensor_pure PA PB PC hA hB hC fB fC hfB hfC eR
    (ringEquivAlgebraRestrictionModuleIso eR eS heS)
    (ringEquivAlgebraRestrictionModuleIso eR eT heT)

end SerrePositivity.BhattScholze
