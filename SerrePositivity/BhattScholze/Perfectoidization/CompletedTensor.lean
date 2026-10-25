module

public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismTensor
public import SerrePositivity.BhattScholze.Perfectoidization.WittPushout
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.CommutativeAlgebra.MappedPrincipalQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorZero
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedSurjectiveAlgebraMul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedQuotientTensorExtension
public import SerrePositivity.BhattScholze.Perfectoidization.TensorPerfectoidization
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationIdentity
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# perfectoid 環の完備テンソル積と有限直積

## 概要
perfectoid 代数の導来完備テンソル積 H⁰ は離散で perfectoid、普遍な perfectoid テンソル、商の完備積、有限直積の perfectoid 性。

## 方針
Fontaine 表示（完全 prism の完備テンソル積）から離散性を得る。

## 規約
有限直積は今 E3（整代数の perfectoid 化）に依存している（ノート BR20）。

## 使われ方
Lemma 10.3、Prop 8.13 の環版、CLMST。
-/

universe u

/-! ## Discreteness and perfectoid H⁰ from the original Fontaine presentations（旧 Perfectoidization/WittPresentation/FontaineCompletedTensorDiscrete.lean） -/

@[expose] public noncomputable section FontaineCompletedTensorDiscrete

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

end FontaineCompletedTensorDiscrete

/-! ## Discreteness and perfectoid H⁰ of the original completed tensor of perfectoid algebras（旧 Perfectoidization/PerfectoidCompletedTensorDiscrete.lean） -/

@[expose] public noncomputable section PerfectoidCompletedTensorDiscrete

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- The original completed tensor is discrete and its actual H⁰ ring is perfectoid.
No p-regularity, finiteness, nonzero, or flatness conditions are added. -/
lemma integralPerfectoid_completedTensor_pure_and_h0
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    ((boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0) ∧
      IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) p := by
  let ORIG := boundedAboveCompletedTensorAlgebra R (p : R) S T
  letI := derivedH0CommRing ORIG
  have hzpure (hz : IsZero ORIG.X.obj) : ORIG.X.obj.IsGE 0 ∧ ORIG.X.obj.IsLE 0 := by
    exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i _ =>
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isZero hz),
      (DerivedCategory.isLE_iff _ _).mpr (fun i _ =>
        (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isZero hz)⟩
  have hzresults (hz : IsZero ORIG.X.obj) :
      (ORIG.X.obj.IsGE 0 ∧ ORIG.X.obj.IsLE 0) ∧
        IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          ORIG.X.obj) p := by
    exact ⟨hzpure hz, Or.inl (ModuleCat.isZero_iff_subsingleton.mp
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map_isZero hz))⟩
  rcases subsingleton_or_nontrivial S with hs0 | hs1
  · exact hzresults (completedTensor_isZero_of_left_isZero R (p : R)
      (ModuleCat.of R S) (ModuleCat.of R T) (ModuleCat.isZero_iff_subsingleton.mpr hs0))
  · letI := hs1
    rcases subsingleton_or_nontrivial T with ht0 | ht1
    · exact hzresults (completedTensor_isZero_of_right_isZero R (p : R)
        (ModuleCat.of R S) (ModuleCat.of R T) (ModuleCat.isZero_iff_subsingleton.mpr ht0))
    · letI := ht1
      letI : Nontrivial R := (algebraMap R S).domain_nontrivial
      rcases hR with hzero | ⟨hpR, hcR, ⟨π, u, hpEq⟩, hFR, hkerR⟩
      · letI := hzero
        exact (zero_ne_one (Subsingleton.elim (0 : R) 1)).elim
      rcases hS with hzero | ⟨hpS, hcS, _, hFS, hkerS⟩
      · letI := hzero
        exact (zero_ne_one (Subsingleton.elim (0 : S) 1)).elim
      rcases hT with hzero | ⟨hpT, hcT, _, hFT, hkerT⟩
      · letI := hzero
        exact (zero_ne_one (Subsingleton.elim (0 : T) 1)).elim
      letI : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
      letI : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
      letI : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
      letI := hcR
      letI := hcS
      letI := hcT
      obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator R p
        hFR hkerR π u hpEq
      exact fontaine_completedTensor_pure_and_h0 p R S T d hd hk hFR hFS hFT hkerS hkerT

/-- The original public discreteness statement is retained. -/
lemma integralPerfectoid_completedTensor_pure
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 := by
  exact (integralPerfectoid_completedTensor_pure_and_h0 p R S T hR hS hT).1

/-- The actual original completed tensor H⁰ ring is integral perfectoid, without
regularity, bounded-torsion, flatness, or nonzero assumptions on the factors. -/
lemma integralPerfectoid_completedTensorH0_isIntegralPerfectoid
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) p := by
  exact (integralPerfectoid_completedTensor_pure_and_h0 p R S T hR hS hT).2

end SerrePositivity.BhattScholze

end PerfectoidCompletedTensorDiscrete

/-! ## The original completed multiplication for perfectoid quotients（旧 Perfectoidization/PerfectoidCompletedQuotientMul.lean） -/

@[expose] public noncomputable section PerfectoidCompletedQuotientMul

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]

/-- A surjective morphism of integral perfectoid rings has invertible completed derived product. -/
lemma integralPerfectoid_completedSurjectiveAlgebraMul_isIso
    (A : Type u) [CommRing A] [Algebra R A]
    (hR : IsIntegralPerfectoid R p) (hA : IsIntegralPerfectoid A p)
    (hs : Function.Surjective (algebraMap R A)) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) A).hom) :=
  completedSurjectiveAlgebraMul_isIso R (p : R) A hs
    (hA.isModuleComplete_algebra R A p)
    (integralPerfectoid_completedTensor_pure p R A A hR hA hA)

/-- The map is exactly the original multiplication on the original perfectoid quotient. -/
lemma integralPerfectoid_completedQuotientMul_isIso (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom) :=
  integralPerfectoid_completedSurjectiveAlgebraMul_isIso p R (R ⧸ I) hR hQ
    Ideal.Quotient.mk_surjective

/-- Complete I-almost zero modules are extension closed for this same quotient ideal. -/
lemma integralPerfectoid_completeIdealExtensionClosed (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    CompleteIdealExtensionClosed R (p : R) I :=
  completeIdealExtensionClosed_of_completed_quotient_mul_isIso (p : R) I
    (integralPerfectoid_completedQuotientMul_isIso p R I hR hQ)

/-- Every original p-power quotient image of I is idempotent, including exponent zero. -/
lemma integralPerfectoid_ideal_mod_power_idempotent (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}))) :=
  ideal_mod_power_idempotent_of_completed_quotient_mul_isIso (p : R) I
    (integralPerfectoid_completedQuotientMul_isIso p R I hR hQ) n

end SerrePositivity.BhattScholze

end PerfectoidCompletedQuotientMul

/-! ## The original completed tensor H⁰ is the universal perfectoid tensor（旧 Perfectoidization/CompletedTensorPerfectoidization.lean）

The unit is normalized by the original actual H⁰ completion unit. The target
retains precisely its original H⁰ ring structure, including zero factors.
-/

@[expose] public noncomputable section CompletedTensorPerfectoidization

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "ORIG" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ORIG).X.obj

/-- The ordinary tensor enters the actual completed H⁰ through the canonical unit comparison. -/
def completedTensorPerfectoidizationMap :
    letI := derivedH0CommRing ORIG
    S ⊗[R] T →+* H := by
  letI := derivedH0CommRing ORIG
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  exact (completedTensorH0PrincipalRingEquiv R p S T).symm.toRingHom.comp
    (principalCompletionUnitRingHom (S ⊗[R] T) (p : S ⊗[R] T))

/-- It is exactly the original H⁰ completion unit, on the standard ordinary tensor classes. -/
lemma completedTensorPerfectoidizationMap_apply (x : S ⊗[R] T) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
    letI := derivedH0CommRing ORIG
    completedTensorPerfectoidizationMap R p S T x =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T))
        ((derivedTensorH0AlgEquiv S T).symm x) := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0CommRing ORIG
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  apply (completedTensorH0PrincipalRingEquiv R p S T).injective
  change completedTensorH0PrincipalRingEquiv R p S T
    ((completedTensorH0PrincipalRingEquiv R p S T).symm _) = _
  rw [RingEquiv.apply_symm_apply, completedTensorH0PrincipalRingEquiv_unit,
    AlgEquiv.apply_symm_apply]

variable [Fact p.Prime]

/-- The same actual map is a perfectoidization; arbitrary perfectoid targets are p-complete. -/
lemma completedTensorPerfectoidizationMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing ORIG
    IsPerfectoidization p (completedTensorPerfectoidizationMap R p S T) := by
  letI := derivedH0CommRing ORIG
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  let e := completedTensorH0PrincipalRingEquiv R p S T
  refine ⟨integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR hS hT, ?_⟩
  intro D _ hD f
  have hc : letI := f.toAlgebra
      IsModuleComplete (S ⊗[R] T) (p : S ⊗[R] T) (ModuleCat.of (S ⊗[R] T) D) := by
    letI := f.toAlgebra
    exact hD.isModuleComplete_algebra (S ⊗[R] T) D p
  obtain ⟨g, hg, huniq⟩ := principalCompletion_existsUnique_ringHom
    (S ⊗[R] T) (p : S ⊗[R] T) D f hc
  refine ⟨g.comp e.toRingHom, ?_, ?_⟩
  · change (g.comp e.toRingHom).comp
      (e.symm.toRingHom.comp (principalCompletionUnitRingHom (S ⊗[R] T) _)) = f
    apply RingHom.ext
    intro x
    change g (e (e.symm (principalCompletionUnitRingHom (S ⊗[R] T) _ x))) = f x
    rw [e.apply_symm_apply]
    exact RingHom.congr_fun hg x
  · intro l hl
    have he : l.comp e.symm.toRingHom = g := by
      apply huniq
      exact hl
    ext x
    have hx := RingHom.congr_fun he (e x)
    change l (e.symm (e x)) = g (e x) at hx
    rw [e.symm_apply_apply] at hx
    exact hx

/-- Comparison with any selected universal perfectoid tensor retains its specified unit. -/
lemma completedTensorPerfectoidizationMap_exists_equiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (D : Type u) [CommRing D] (f : S ⊗[R] T →+* D) (hf : IsPerfectoidization p f) :
    letI := derivedH0CommRing ORIG
    ∃ e : H ≃+* D, e.toRingHom.comp (completedTensorPerfectoidizationMap R p S T) = f := by
  letI := derivedH0CommRing ORIG
  exact (completedTensorPerfectoidizationMap_isPerfectoidization R p S T hR hS hT).exists_equiv p hf

/-- Actual completed tensor H⁰ realizes perfectoidization after changing the base
of any specified universal perfectoidization map. -/
lemma completedTensorBaseChangeMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (A : Type u) [CommRing A] [Algebra R A] (f : A →ₐ[R] S)
    (hf : IsPerfectoidization p f.toRingHom) :
    letI := derivedH0CommRing ORIG
    IsPerfectoidization p (perfectoidizationTensorBaseChangeMap f
      (completedTensorPerfectoidizationMap R p S T)) := by
  letI := derivedH0CommRing ORIG
  exact perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf _
    (completedTensorPerfectoidizationMap_isPerfectoidization R p S T hR hf.1 hT)

/-- The original actual H⁰ unit has the same mod-p bijectivity as the established
perfectoid tensor model, transported through a unit-preserving universal equivalence. -/
lemma completedTensorPerfectoidizationMap_modP_bijective
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing ORIG
    Function.Bijective (modPMap p (completedTensorPerfectoidizationMap R p S T)) := by
  letI := derivedH0CommRing ORIG
  obtain ⟨D, hD, F, hF, hbij⟩ :=
    exists_perfectoidTensorPerfectoidization_modP p R S T hR hS hT
  letI := hD
  obtain ⟨e, he⟩ := completedTensorPerfectoidizationMap_exists_equiv R p S T hR hS hT D F hF
  let ep : ModP H p ≃+* ModP D p := Ideal.quotientEquiv _ _ e
    (by simp only [Ideal.map_span, Set.image_singleton, map_natCast])
  have hep (x : ModP (S ⊗[R] T) p) :
      ep (modPMap p (completedTensorPerfectoidizationMap R p S T) x) = modPMap p F x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (e (completedTensorPerfectoidizationMap R p S T x)) =
      Ideal.Quotient.mk _ (F x)
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun he x)
  constructor
  · intro x y hxy
    apply hbij.1
    rw [← hep x, ← hep y, hxy]
  · intro z
    obtain ⟨x, hx⟩ := hbij.2 (ep z)
    refine ⟨x, ep.injective ?_⟩
    rw [hep x, hx]

end SerrePositivity.BhattScholze

end CompletedTensorPerfectoidization

/-! ## Perfectoid tests of the original completed tensor H⁰（旧 Perfectoidization/CompletedTensorPerfectoidUniversal.lean）

Use the existing G2 principal-completion comparison and its universal property.
No discreteness of the original tensor, bounded torsion, or classical-completion
comparison is assumed. This is the ring-valued part needed for BS Prop. 8.13.
-/

@[expose] public noncomputable section CompletedTensorPerfectoidUniversal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "C" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (C).X.obj

/-- Every map from the ordinary tensor to a perfectoid ring extends uniquely
over the actual H⁰ completion unit, including for unbounded p-power torsion. -/
lemma existsUnique_completedTensorPerfectoidLift
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) (f : S ⊗[R] T →+* D) :
    letI := derivedH0CommRing C
    ∃! g : H →+* D, g.comp (completedTensorPerfectoidizationMap R p S T) = f := by
  let := derivedH0CommRing C
  let := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  let e := completedTensorH0PrincipalRingEquiv R p S T
  have hc : letI := f.toAlgebra
      IsModuleComplete (S ⊗[R] T) (p : S ⊗[R] T) (ModuleCat.of (S ⊗[R] T) D) := by
    let := f.toAlgebra
    exact hD.isModuleComplete_algebra (S ⊗[R] T) D p
  obtain ⟨g, hg, huniq⟩ := principalCompletion_existsUnique_ringHom
    (S ⊗[R] T) (p : S ⊗[R] T) D f hc
  refine ⟨g.comp e.toRingHom, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change g (e (e.symm (principalCompletionUnitRingHom (S ⊗[R] T) _ x))) = f x
    rw [e.apply_symm_apply]
    exact RingHom.congr_fun hg x
  · intro l hl
    have he : l.comp e.symm.toRingHom = g := huniq _ hl
    ext x
    have hx := RingHom.congr_fun he (e x)
    change l (e.symm (e x)) = g (e x) at hx
    change l x = g (e x)
    simpa only [e.symm_apply_apply] using hx

/-- Maps from the original completed tensor H⁰ to a perfectoid ring are
determined by their composition with the original ordinary-tensor unit. -/
lemma completedTensorPerfectoid_hom_ext
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) :
    letI := derivedH0CommRing C
    ∀ f g : H →+* D,
      f.comp (completedTensorPerfectoidizationMap R p S T) =
        g.comp (completedTensorPerfectoidizationMap R p S T) → f = g := by
  let := derivedH0CommRing C
  intro f g hfg
  exact (existsUnique_completedTensorPerfectoidLift R p S T D hD
    (f.comp (completedTensorPerfectoidizationMap R p S T))).unique rfl hfg.symm

/-- The specified map is extended over the same actual H⁰ completion unit. -/
def completedTensorPerfectoidLift
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) (f : S ⊗[R] T →+* D) :
    letI := derivedH0CommRing C
    H →+* D :=
  (existsUnique_completedTensorPerfectoidLift R p S T D hD f).choose

/-- The extension retains its specified original-tensor map. -/
lemma completedTensorPerfectoidLift_comp
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) (f : S ⊗[R] T →+* D) :
    letI := derivedH0CommRing C
    (completedTensorPerfectoidLift R p S T D hD f).comp
      (completedTensorPerfectoidizationMap R p S T) = f :=
  (existsUnique_completedTensorPerfectoidLift R p S T D hD f).choose_spec.1

/-- A ring-perfectoidization of the ordinary tensor is also one of the actual
completed tensor H⁰, via the extension of the very same unit. -/
lemma completedTensorPerfectoidLift_isPerfectoidization
    (D : Type u) [CommRing D] (f : S ⊗[R] T →+* D) (hf : IsPerfectoidization p f) :
    letI := derivedH0CommRing C
    IsPerfectoidization p (completedTensorPerfectoidLift R p S T D hf.1 f) := by
  let := derivedH0CommRing C
  refine ⟨hf.1, ?_⟩
  intro U _ hU k
  obtain ⟨l, hl, huniq⟩ := hf.2 U hU
    (k.comp (completedTensorPerfectoidizationMap R p S T))
  refine ⟨l, ?_, ?_⟩
  · apply completedTensorPerfectoid_hom_ext R p S T U hU
    rw [RingHom.comp_assoc, completedTensorPerfectoidLift_comp, hl]
  · intro m hm
    apply huniq
    rw [← completedTensorPerfectoidLift_comp R p S T D hf.1 f,
      ← RingHom.comp_assoc, hm]

end SerrePositivity.BhattScholze

end CompletedTensorPerfectoidUniversal

/-! ## Finite products from the existing universal integral-perfectoidization input（旧 Perfectoidization/PerfectoidFiniteProduct.lean）

Coordinate maps to the original perfectoid ring give a retraction of the
chosen universal object. Universality makes this a two-sided inverse. This
proof explicitly retains the existing B-I existence dependency.
-/

@[expose] public noncomputable section PerfectoidFiniteProduct

namespace SerrePositivity.BhattScholze

/-- A finite product of copies of a perfectoid ring is perfectoid, including the
empty product. This proof uses the existing integral-existence input B-I. -/
theorem isIntegralPerfectoid_finPi
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ) : IsIntegralPerfectoid (Fin r → R) p := by
  obtain ⟨C, hC, f, hf⟩ := Inputs.exists_perfectoidization_of_integral R (Fin r → R) p hR
  let := hC
  let k : C →+* (Fin r → R) :=
    RingHom.pi fun i => hf.lift hR (Pi.evalRingHom (fun _ : Fin r => R) i)
  have hkf : k.comp f = RingHom.id (Fin r → R) := by
    apply RingHom.ext
    intro x
    apply funext
    intro i
    exact RingHom.congr_fun (hf.lift_comp hR (Pi.evalRingHom (fun _ : Fin r => R) i)) x
  have hfk : f.comp k = RingHom.id C := by
    obtain ⟨l, _hl, hu⟩ := hf.2 C hf.1 f
    exact (hu (f.comp k) (by
      change (f.comp k).comp f = f
      rw [RingHom.comp_assoc, hkf, RingHom.comp_id])).trans
      (hu (RingHom.id C) (RingHom.id_comp f)).symm
  let e : (Fin r → R) ≃+* C :=
    { f with invFun := k
             left_inv := fun x => RingHom.congr_fun hkf x
             right_inv := fun x => RingHom.congr_fun hfk x }
  exact isIntegralPerfectoid_of_ringEquiv p e.symm hf.1

/-- Any specified universal perfectoidization of the finite product is its
original unit as an algebra equivalence over the original base. -/
theorem finiteProduct_perfectoidization_exists_algEquiv
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ e : (Fin r → R) ≃ₐ[R] C, e.toAlgHom = f := by
  obtain ⟨e, he⟩ := (isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id.exists_equiv p hf
  have hef : e.toRingHom = f.toRingHom := by simpa only [RingHom.comp_id] using he
  let e' : (Fin r → R) ≃ₐ[R] C := AlgEquiv.ofRingEquiv (f := e) fun s => by
    change e.toRingHom (algebraMap R (Fin r → R) s) = algebraMap R C s
    rw [hef]
    exact f.commutes s
  exact ⟨e', by ext x; exact RingHom.congr_fun hef x⟩

end SerrePositivity.BhattScholze

end PerfectoidFiniteProduct
