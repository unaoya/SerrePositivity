module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.CommutativeAlgebra.MappedPrincipalQuotient
public import SerrePositivity.BhattScholze.Perfectoidization.Tensor.PerfectPrismTensor
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAlgebraCongruence
public import SerrePositivity.HomologicalAlgebra.RingEquivDerivedTensor

/-!
# 完全 prism の射の剰余因子と剰余テンソル

## 概要
完全 prism の射の剰余因子の代数同型と、各 prism 自身の剰余環を使う Cartier テンソル比較、係数表示への移送。
BS 著者版 Lemma 3.5 と Theorem 3.10 に関わる、完全 prism の射の剰余テンソルを比較する。

## 方針
完全 prism の Cartier 比較を剰余因子で書き換える。

## 規約
今は主定理の経路にない。

## 使われ方
完全 prism の完備テンソル積の比較。
-/

universe u

/-! ## Original residue factors of a morphism of perfect prisms -/

@[expose] public noncomputable section PerfectPrismResidueFactor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
attribute [local instance] adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]

/-- The extended base ideal gives the target prism's own residue ring, with
the coefficient action induced by the original prism morphism. -/
def perfectPrismResidueFactorAlgEquiv
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S) :
    letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
    (S ⧸ Ideal.map (algebraMap R S) PR.ideal) ≃ₐ[R ⧸ PR.ideal] S ⧸ PS.ideal := by
  letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
  have hi : Ideal.map (algebraMap R S) PR.ideal = PS.ideal := by
    rw [← hf]
    exact f.map_ideal_eq
  let e := Ideal.quotientEquivAlgOfEq R hi
  exact
    { e.toRingEquiv with
      commutes' x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change e (Ideal.Quotient.mk _ (algebraMap R S r)) =
          f.quotientMap (Ideal.Quotient.mk PR.ideal r)
        rw [Ideal.quotientEquivAlgOfEq_mk, OrientedPrism.Hom.quotientMap_mk, hf] }

/-- The factor comparison sends each original representative to itself. -/
lemma perfectPrismResidueFactorAlgEquiv_mk
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S) (s : S) :
    perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) PR.ideal) s) =
      Ideal.Quotient.mk PS.ideal s := rfl

/-- The inverse comparison retains the same representative as well. -/
lemma perfectPrismResidueFactorAlgEquiv_symm_mk
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S) (s : S) :
    letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
    (perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf).symm
        (Ideal.Quotient.mk PS.ideal s) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) PR.ideal) s := by
  letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
  apply (perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf).injective
  rw [AlgEquiv.apply_symm_apply, perfectPrismResidueFactorAlgEquiv_mk]

/-- The coefficient map after comparison is precisely the original prism quotient map. -/
lemma perfectPrismResidueFactorAlgEquiv_algebraMap
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S)
    (x : R ⧸ PR.ideal) :
    perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf
        (algebraMap (R ⧸ PR.ideal) (S ⧸ Ideal.map (algebraMap R S) PR.ideal) x) =
      f.quotientMap x := by
  letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
  exact (perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf).commutes x

end SerrePositivity.BhattScholze

end PerfectPrismResidueFactor

/-! ## Cartier tensor comparison using each perfect prism's own residue ring -/

@[expose] public noncomputable section PerfectPrismCartierTensorComparison

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
      (PR.isDistinguished_generator))

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
    (PR.isDistinguished_generator)
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
      (PR.isDistinguished_generator))

end SerrePositivity.BhattScholze

end PerfectPrismCartierTensorComparison

/-! ## Transport the actual perfect-prism residue tensor to presented coefficient rings -/

@[expose] public noncomputable section PerfectPrismResidueTensorTransport

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

end PerfectPrismResidueTensorTransport
