module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaTensor
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Perfectoidization.Tensor.IteratedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularCompletionPure
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
public import SerrePositivity.HomologicalAlgebra.RingEquivDerivedTensor

/-!
# 完全 prism の完備テンソル積とその Cartier 商

## 概要
完全 δ 環の反復完備テンソル積 H⁰ の完全 prism 構造と離散性、Cartier 商と完備剰余テンソルの比較（代数同型）、剰余表示の移送。

## 方針
完全 δ 環のテンソル積（Delta/Perfect/PerfectDeltaTensor）を (p,d) 完備化し、商を比較する。

## 規約
圏の余積としての普遍性は述べない。

## 使われ方
perfectoid 環の完備テンソル積（Perfectoidization/CompletedTensor）、BS 著者版 Proposition 8.13 の環版。
-/

universe u

/-! ## Perfect delta structure and prism on original iterated completed tensor H⁰

The original H⁰ ring, base action and second completion unit are retained.
Discreteness of the second derived object and its Cartier quotient comparison
are separate subsequent steps.
-/

@[expose] public noncomputable section PerfectDeltaIteratedTensorH0

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R)
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AP).X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
local notation "DB" => perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R d AP)
/-- The existing original iterated completed H⁰ ring carries a perfect delta structure. -/
def perfectDeltaIteratedTensorH0Structure :
    letI := derivedH0CommRing AD
    DeltaStructure p C := by
  letI := derivedH0CommRing AP
  letI := derivedH0Algebra AP
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := completionH0ScalarAlgebra R d AP
  letI := pdCompletionCommRing B p (algebraMap R B d)
  letI := pdCompletionAlgebra B p (algebraMap R B d)
  exact (deltaPDCompletionStructure DB (algebraMap R B d)).comapEquiv
    (iteratedCompletedTensorH0PDAlgEquiv R p d S T).toRingEquiv

local notation "DC" => perfectDeltaIteratedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT d

/-- The transported delta structure on the original H⁰ is perfect. -/
lemma perfectDeltaIteratedTensorH0Structure_isPerfect :
    letI := derivedH0CommRing AD
    (DC).IsPerfect := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := completionH0ScalarAlgebra R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  exact (deltaPDCompletionStructure_isPerfect DB
    (perfectDeltaCompletedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT)
    (algebraMap R B d)).comapEquiv
      (iteratedCompletedTensorH0PDAlgEquiv R p d S T).toRingEquiv

/-- The exact standard F3 comparison is a delta map. -/
lemma perfectDeltaIteratedTensorH0Structure_comparison_isDeltaHom :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := completionH0ScalarAlgebra R d AP
    letI := pdCompletionCommRing B p (algebraMap R B d)
    letI := pdCompletionAlgebra B p (algebraMap R B d)
    (DC).IsDeltaHom (deltaPDCompletionStructure DB (algebraMap R B d))
      (iteratedCompletedTensorH0PDAlgEquiv R p d S T).toRingEquiv.toRingHom := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := completionH0ScalarAlgebra R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  exact (deltaPDCompletionStructure DB (algebraMap R B d)).comapEquiv_isDeltaHom
    (iteratedCompletedTensorH0PDAlgEquiv R p d S T).toRingEquiv

/-- The original second H⁰ completion unit is a delta map. -/
lemma perfectDeltaIteratedTensorH0Structure_unit_isDeltaHom :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DB).IsDeltaHom DC (J).toRingHom := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := completionH0ScalarAlgebra R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  let e := (iteratedCompletedTensorH0PDAlgEquiv R p d S T).toRingEquiv
  have h := ((deltaPDCompletionStructure DB (algebraMap R B d)).comapEquiv_symm_isDeltaHom e).comp
    (pdCompletionUnit_isDeltaHom DB (algebraMap R B d))
  have hj : e.symm.toRingHom.comp (pdCompletionUnit B p (algebraMap R B d)) =
      (J).toRingHom := by
    apply RingHom.ext
    intro x
    apply e.injective
    change e (e.symm (pdCompletionUnit B p (algebraMap R B d) x)) = e (J x)
    rw [e.apply_symm_apply]
    exact (iteratedCompletedTensorH0PDAlgEquiv_unit R p d S T x).symm
  rw [hj] at h
  exact h

/-- The original R-algebra map remains a delta map after both completions. -/
lemma perfectDeltaIteratedTensorH0Structure_base_isDeltaHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    DR.IsDeltaHom DC (algebraMap R C) := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := completionH0ScalarAlgebra R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  have h := (perfectDeltaIteratedTensorH0Structure_unit_isDeltaHom p R S T
    DR DS DT hR hS hT hRS hRT d).comp
    (perfectDeltaCompletedTensorH0Structure_base_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)
  have hj : (J).toRingHom.comp (algebraMap R B) = algebraMap R C := by
    ext r
    exact (J).commutes r
  rw [hj] at h
  exact h

/-- The original distinguished base element has its original distinguished image. -/
lemma perfectDeltaIteratedTensorH0Structure_distinguished (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DC).IsDistinguished (algebraMap R C d) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  exact (perfectDeltaIteratedTensorH0Structure_base_isDeltaHom p R S T
    DR DS DT hR hS hT hRS hRT d).map_isDistinguished hd

/-- A perfect prism on the original actual iterated completed H⁰, with original generator. -/
def perfectDeltaIteratedTensorH0Prism (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AD
    OrientedPrism p C := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  have hp := iteratedCompletedTensorH0_self_complete_p R p d S T
  have hc := iteratedCompletedTensorH0_self_complete_d R p d S T
  have hperf := perfectDeltaIteratedTensorH0Structure_isPerfect p R S T
    DR DS DT hR hS hT hRS hRT d
  letI : IsAdicComplete (Ideal.span {(p : C)}) C :=
    (isRingModuleComplete_iff_isAdicComplete_natCast C p hperf.p_mul_injective).mp hp
  have hdist := perfectDeltaIteratedTensorH0Structure_distinguished p R S T
    DR DS DT hR hS hT hRS hRT d hd
  exact OrientedPrism.ofDistinguished DC (algebraMap R C d) hdist
    (hperf.distinguished_mul_injective hdist) hp hc

/-- The prism has exactly the original image of d as its chosen generator. -/
lemma perfectDeltaIteratedTensorH0Prism_generator (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (perfectDeltaIteratedTensorH0Prism p R S T DR DS DT hR hS hT hRS hRT d hd).generator =
      algebraMap R C d := rfl

/-- Its delta structure is the proved transported perfect delta structure. -/
lemma perfectDeltaIteratedTensorH0Prism_isPerfect (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AD
    (perfectDeltaIteratedTensorH0Prism p R S T
      DR DS DT hR hS hT hRS hRT d hd).deltaStructure.IsPerfect :=
  perfectDeltaIteratedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT d

/-- The standard H⁰ comparison is a morphism to the existing standard PD prism. -/
def perfectDeltaIteratedTensorH0PrismComparison (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := completionH0ScalarAlgebra R d AP
    letI := pdCompletionCommRing B p (algebraMap R B d)
    letI := pdCompletionAlgebra B p (algebraMap R B d)
    OrientedPrism.Hom
      (perfectDeltaIteratedTensorH0Prism p R S T DR DS DT hR hS hT hRS hRT d hd)
      (perfectDeltaPDPrism DB
        (perfectDeltaCompletedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT)
        (algebraMap R B d)
        (perfectDeltaCompletedTensorH0Structure_distinguished p R S T
          DR DS DT hR hS hT hRS hRT d hd)) := by
  letI := derivedH0CommRing AP
  letI := derivedH0Algebra AP
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := completionH0ScalarAlgebra R d AP
  letI := pdCompletionCommRing B p (algebraMap R B d)
  letI := pdCompletionAlgebra B p (algebraMap R B d)
  refine
    { toRingHom := (iteratedCompletedTensorH0PDAlgEquiv R p d S T).toRingEquiv.toRingHom
      map_delta := perfectDeltaIteratedTensorH0Structure_comparison_isDeltaHom p R S T
        DR DS DT hR hS hT hRS hRT d
      ideal_le := ?_ }
  apply Ideal.span_le.mpr
  intro x hx
  have hx' : x = algebraMap R C d := Set.mem_singleton_iff.mp hx
  subst x
  change iteratedCompletedTensorH0PDAlgEquiv R p d S T (algebraMap R C d) ∈
    Ideal.span {pdCompletionUnit B p (algebraMap R B d) (algebraMap R B d)}
  rw [iteratedCompletedTensorH0PDAlgEquiv_algebraMap]
  exact Ideal.subset_span (by simp)

/-- This standard prism comparison is an isomorphism on its original underlying rings. -/
lemma perfectDeltaIteratedTensorH0PrismComparison_bijective (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := completionH0ScalarAlgebra R d AP
    letI := pdCompletionCommRing B p (algebraMap R B d)
    letI := pdCompletionAlgebra B p (algebraMap R B d)
    Function.Bijective
      (perfectDeltaIteratedTensorH0PrismComparison p R S T
        DR DS DT hR hS hT hRS hRT d hd).toRingHom := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := completionH0ScalarAlgebra R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  exact (iteratedCompletedTensorH0PDAlgEquiv R p d S T).bijective

include hR hS hT hRS hRT in
/-- The actual standard Cartier quotient of the original iterated H⁰ is integral perfectoid. -/
lemma perfectDeltaIteratedTensorH0_quotient_isIntegralPerfectoid (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    IsIntegralPerfectoid (C ⧸ Ideal.span {algebraMap R C d}) p := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  exact (perfectDeltaIteratedTensorH0Prism p R S T
    DR DS DT hR hS hT hRS hRT d hd).quotient_isIntegralPerfectoid
    (perfectDeltaIteratedTensorH0Prism_isPerfect p R S T DR DS DT hR hS hT hRS hRT d hd)

end SerrePositivity.BhattScholze

end PerfectDeltaIteratedTensorH0

/-! ## Discreteness of the original p,d completed tensor of perfect delta rings -/

@[expose] public noncomputable section PerfectDeltaIteratedTensorDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP

include hR hS hT hRS hRT hd in
/-- The original p-completed tensor followed by actual d-completion is concentrated
in degree zero. -/
lemma perfectDelta_iteratedTensor_pure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0 := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  have h := perfectDelta_completedTensor_pure p R S T DR DS DT hR hS hT
  let hge : (AP).X.obj.IsGE 0 := h.1
  let hle : (AP).X.obj.IsLE 0 := h.2.1
  have hreg := perfectDeltaCompletedTensorH0Structure_distinguished_regular p R S T
    DR DS DT hR hS hT hRS hRT d hd
  apply derivedAlgebra_completion_pure_of_h0_regular R d AP
  simpa only [IsSMulRegular, smul_eq_mul] using hreg

/-- Combine actual discreteness with the perfect prism on its unchanged actual H⁰. -/
lemma perfectDelta_iteratedTensor_discrete_perfect :
    letI := derivedH0CommRing AD
    (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0 ∧
      (perfectDeltaIteratedTensorH0Prism p R S T
        DR DS DT hR hS hT hRS hRT d hd).deltaStructure.IsPerfect := by
  let := derivedH0CommRing AD
  have h := perfectDelta_iteratedTensor_pure p R S T DR DS DT hR hS hT hRS hRT d hd
  exact ⟨h.1, h.2, perfectDeltaIteratedTensorH0Prism_isPerfect p R S T
    DR DS DT hR hS hT hRS hRT d hd⟩

end SerrePositivity.BhattScholze

end PerfectDeltaIteratedTensorDiscrete

/-! ## The actual Cartier quotient as the original completed residue tensor

All objects and quotient actions are the original ones. This first comparison
is in the derived category of modules; multiplicative compatibility is separate.
-/

@[expose] public noncomputable section PerfectDeltaCartierTensorComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
local notation "RES" => boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ

/-- The original p-completed tensor of both ordinary residue factors is the actual Cartier quotient. -/
def perfectDelta_completedResidueTensorCartierIso :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (RES).X.obj ≅ (DerivedCategory.singleFunctor (ModuleCat Q) 0).obj
      (ModuleCat.of Q (C ⧸ Ideal.span {algebraMap R C d})) := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  have hpure := perfectDelta_iteratedTensor_pure p R S T DR DS DT hR hS hT hRS hRT d hd
  let hge : (AD).X.obj.IsGE 0 := hpure.1
  let hle : (AD).X.obj.IsLE 0 := hpure.2
  have hr : IsSMulRegular R d := by
    simpa only [IsSMulRegular, smul_eq_mul] using hR.distinguished_mul_injective hd
  have hs : IsSMulRegular S d := by
    intro x y hxy
    apply hS.distinguished_mul_injective (hRS.map_isDistinguished hd)
    simpa only [Algebra.smul_def] using hxy
  have ht : IsSMulRegular T d := by
    intro x y hxy
    apply hT.distinguished_mul_injective (hRT.map_isDistinguished hd)
    simpa only [Algebra.smul_def] using hxy
  have hc : IsSMulRegular C d := by
    intro x y hxy
    apply (perfectDeltaIteratedTensorH0Prism p R S T
      DR DS DT hR hS hT hRS hRT d hd).generator_regular
    change algebraMap R C d * x = algebraMap R C d * y
    simpa only [Algebra.smul_def] using hxy
  let e := (regularIteratedCompletedTensorQuotientIso R (p : R) d hr S T hs ht).symm ≪≫
    DerivedCategory.Minus.ι.mapIso (pureDerivedAlgebraCartierQuotientIso R d hr AD hc)
  have aux (c : Q) (h : (q) (p : R) = c) :
      (derivedComplexCompletionFunctor Q c).obj
          (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj ≅
        (DerivedCategory.singleFunctor (ModuleCat Q) 0).obj
          (ModuleCat.of Q (C ⧸ Ideal.span {algebraMap R C d})) := by
    subst c
    exact e
  exact aux (p : Q) (map_natCast (q) p)

include hR hS hT hRS hRT hd in
/-- The original residue tensor is derived-discrete, with no residue flatness assumption. -/
lemma perfectDelta_completedResidueTensor_pure :
    (RES).X.obj.IsGE 0 ∧ (RES).X.obj.IsLE 0 := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let e := perfectDelta_completedResidueTensorCartierIso p R S T
    DR DS DT hR hS hT hRS hRT d hd
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (RES).X.obj) :=
    (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso e)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega))⟩

/-- Actual residue-tensor H⁰ and the ordinary Cartier quotient agree as quotient-base modules. -/
def perfectDelta_completedResidueTensorCartierH0Iso :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RES).X.obj ≅
      ModuleCat.of Q (C ⧸ Ideal.span {algebraMap R C d}) := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (perfectDelta_completedResidueTensorCartierIso p R S T
        DR DS DT hR hS hT hRS hRT d hd) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).app _

/-- The existing comparison is the common original linear map, independently of proof choices. -/
lemma perfectDelta_completedResidueTensorCartierH0Iso_eq_common
    (hr : IsSMulRegular R d)
    (hs : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (ht : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hc : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    perfectDelta_completedResidueTensorCartierH0Iso p R S T
        DR DS DT hR hS hT hRS hRT d hd =
      iteratedCompletedTensorCartierH0Iso R (p : R) d hr S T hs ht hc hpure := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  rw [iteratedCompletedTensorCartierH0Iso_eq_derived]
  rfl

end SerrePositivity.BhattScholze

end PerfectDeltaCartierTensorComparison

/-! ## The original Cartier quotient supplies the actual completed residue-tensor algebra map -/

@[expose] public noncomputable section PerfectDeltaCartierTensorAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "RES" => boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ

include hR hS hT hRS hRT hd in
/-- The literal original Cartier quotient is p-adically complete, with p-torsion allowed. -/
lemma perfectDelta_iteratedTensorCartier_isAdicComplete :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    IsAdicComplete (Ideal.span {(p : CQ)}) CQ := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let P := perfectDeltaIteratedTensorH0Prism p R S T DR DS DT hR hS hT hRS hRT d hd
  have hP := perfectDeltaIteratedTensorH0Prism_isPerfect p R S T
    DR DS DT hR hS hT hRS hRT d hd
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_quotient_isAdicComplete
    (perfectDeltaIteratedTensorH0Structure_distinguished p R S T
      DR DS DT hR hS hT hRS hRT d hd)

include hR hS hT hRS hRT hd in
/-- The exact quotient-base derived completeness required by the common algebra extension. -/
lemma perfectDelta_iteratedTensorCartier_isModuleComplete :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    IsModuleComplete Q ((q) (p : R)) (ModuleCat.of Q CQ) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := perfectDelta_iteratedTensorCartier_isAdicComplete p R S T
    DR DS DT hR hS hT hRS hRT d hd
  have hc : IsModuleComplete CQ (p : CQ) (ModuleCat.of CQ CQ) :=
    isModuleComplete_of_isAdicComplete CQ (p : CQ) (ModuleCat.of CQ CQ)
  have hc' : IsModuleComplete CQ (algebraMap Q CQ (p : Q)) (ModuleCat.of CQ CQ) := by
    simpa only [map_natCast] using hc
  rw [map_natCast]
  exact (isModuleComplete_algebraMap_iff Q CQ (p : Q) CQ).mp hc'

/-- The standard residue-tensor algebra map on its actual completed H⁰, with all inputs supplied. -/
def perfectDelta_completedResidueTensorCartierAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RES).X.obj →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  let k := iteratedTensorCartierCompletedAlgHom R (p : R) d S T
    (perfectDelta_iteratedTensorCartier_isModuleComplete p R S T
      DR DS DT hR hS hT hRS hRT d hd)
  have aux (c : Q) (hc : (q) (p : R) = c) :
      letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        (boundedAboveCompletedTensorAlgebra Q c SQ TQ).X.obj →ₐ[Q] CQ := by
    subst c
    exact k
  exact aux (p : Q) (map_natCast (q) p)

local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ

/-- Scalar normalization preserves the original completed residue-tensor unit diagram. -/
lemma perfectDelta_completedResidueTensorCartierAlgHom_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RX).X.obj) :
    let := derivedH0CommRing AD
    let := derivedH0Algebra AD
    let := derivedH0CommRing RX
    let := derivedH0Algebra RX
    let := derivedH0CommRing RES
    let := derivedH0Algebra RES
    perfectDelta_completedResidueTensorCartierAlgHom p R S T
        DR DS DT hR hS hT hRS hRT d hd
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q (p : Q) RX) x) =
      iteratedTensorCartierTensorAlgHom R (p : R) d S T
        (derivedTensorH0AlgEquiv (R := Q) SQ TQ x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let hp := perfectDelta_iteratedTensorCartier_isModuleComplete p R S T
    DR DS DT hR hS hT hRS hRT d hd
  let k := iteratedTensorCartierCompletedAlgHom R (p : R) d S T hp
  let lift (c : Q) (hc : (q) (p : R) = c) :
      let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        (boundedAboveCompletedTensorAlgebra Q c SQ TQ).X.obj →ₐ[Q] CQ := by
    subst c
    exact k
  have aux (c : Q) (hc : (q) (p : R) = c) :
      let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      lift c hc (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q c RX) x) =
        iteratedTensorCartierTensorAlgHom R (p : R) d S T
          (derivedTensorH0AlgEquiv (R := Q) SQ TQ x) := by
    subst c
    exact iteratedTensorCartierCompletedAlgHom_unit R (p : R) d S T hp x
  exact aux (p : Q) (map_natCast (q) p)

/-- Completed pure tensors of the original residue representatives keep their factor images. -/
lemma perfectDelta_completedResidueTensorCartierAlgHom_unit_tmul (s : S) (t : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    perfectDelta_completedResidueTensorCartierAlgHom p R S T
        DR DS DT hR hS hT hRS hRT d hd
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q (p : Q) RX)
          ((derivedTensorH0AlgEquiv (R := Q) SQ TQ).symm
            (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
              Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0LeftAlgHom R (p : R) d S T s) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0RightAlgHom R (p : R) d S T t) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing RES
  let := derivedH0Algebra RES
  rw [perfectDelta_completedResidueTensorCartierAlgHom_unit,
    AlgEquiv.apply_symm_apply, iteratedTensorCartierTensorAlgHom_tmul]

end SerrePositivity.BhattScholze

end PerfectDeltaCartierTensorAlgebra

/-! ## The actual perfect-prism Cartier tensor comparison as an algebra isomorphism -/

@[expose] public noncomputable section PerfectDeltaCartierTensorAlgEquiv

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (p : ℕ) [hpPrime : Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [hRc : IsAdicComplete (Ideal.span {(p : R)}) R]
    [hSc : IsAdicComplete (Ideal.span {(p : S)}) S]
    [hTc : IsAdicComplete (Ideal.span {(p : T)}) T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "RES" => boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ

include hpPrime hRc hSc hTc hR hS hT hRS hRT hd in
lemma perfectDelta_cartierTensor_inputs :
    IsSMulRegular R d ∧
      scalarExtensionTorVanishing (q) (ModuleCat.of R S) ∧
      scalarExtensionTorVanishing (q) (ModuleCat.of R T) ∧
      IsSMulRegular C d ∧ ((AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  have hr : IsSMulRegular R d := by
    simpa only [IsSMulRegular, smul_eq_mul] using hR.distinguished_mul_injective hd
  have hs : IsSMulRegular S d := by
    intro x y hxy
    apply hS.distinguished_mul_injective (hRS.map_isDistinguished hd)
    simpa only [Algebra.smul_def] using hxy
  have ht : IsSMulRegular T d := by
    intro x y hxy
    apply hT.distinguished_mul_injective (hRT.map_isDistinguished hd)
    simpa only [Algebra.smul_def] using hxy
  have hc : IsSMulRegular C d := by
    intro x y hxy
    apply (perfectDeltaIteratedTensorH0Prism p R S T
      DR DS DT hR hS hT hRS hRT d hd).generator_regular
    change algebraMap R C d * x = algebraMap R C d * y
    simpa only [Algebra.smul_def] using hxy
  exact ⟨hr, scalarExtensionTorVanishing_principal_of_regular d hr (ModuleCat.of R S) hs,
    scalarExtensionTorVanishing_principal_of_regular d hr (ModuleCat.of R T) ht, hc,
    perfectDelta_iteratedTensor_pure p R S T DR DS DT hR hS hT hRS hRT d hd⟩

/-- The standard completed residue-tensor map is an algebra isomorphism
to the original Cartier quotient. -/
def perfectDelta_completedResidueTensorCartierAlgEquiv :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RES).X.obj ≃ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
  letI := derivedH0CommRing RES
  letI := derivedH0Algebra RES
  have h := perfectDelta_cartierTensor_inputs p R S T DR DS DT hR hS hT hRS hRT d hd
  exact iteratedTensorCartierCompletedAlgEquiv R (p : R) d h.1 S T h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2
    (perfectDelta_iteratedTensorCartier_isModuleComplete p R S T
      DR DS DT hR hS hT hRS hRT d hd)

/-- It retains exactly the existing standard algebra map, with the original units and factors. -/
lemma perfectDelta_completedResidueTensorCartierAlgEquiv_toAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (perfectDelta_completedResidueTensorCartierAlgEquiv p R S T
      DR DS DT hR hS hT hRS hRT d hd).toAlgHom =
      perfectDelta_completedResidueTensorCartierAlgHom p R S T
        DR DS DT hR hS hT hRS hRT d hd := by
  rfl

/-- The original established linear isomorphism, including its inverse, is unchanged. -/
lemma perfectDelta_completedResidueTensorCartierAlgEquiv_toLinearEquiv :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (perfectDelta_completedResidueTensorCartierAlgEquiv p R S T
      DR DS DT hR hS hT hRS hRT d hd).toLinearEquiv =
      (perfectDelta_completedResidueTensorCartierH0Iso p R S T
        DR DS DT hR hS hT hRS hRT d hd).toLinearEquiv := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing RES
  let := derivedH0Algebra RES
  have h := perfectDelta_cartierTensor_inputs p R S T DR DS DT hR hS hT hRS hRT d hd
  have h1 := iteratedTensorCartierCompletedAlgEquiv_toLinearEquiv R (p : R) d h.1 S T
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    (perfectDelta_iteratedTensorCartier_isModuleComplete p R S T
      DR DS DT hR hS hT hRS hRT d hd)
  have h2 := perfectDelta_completedResidueTensorCartierH0Iso_eq_common p R S T
    DR DS DT hR hS hT hRS hRT d hd h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  exact h1.trans (congrArg (fun e => e.toLinearEquiv) h2).symm

end SerrePositivity.BhattScholze

end PerfectDeltaCartierTensorAlgEquiv

/-! ## The original completed tensor H⁰ under compatible perfect-delta residue presentations

The comparison is a ring equivalence through the original ordinary tensors and
their actual completion units. It does not require p-regularity of these tensors.
-/

@[expose] public noncomputable section PerfectDeltaPresentedTensorRing

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

end PerfectDeltaPresentedTensorRing

/-! ## Residue presentations of perfect delta rings and the original completed tensor -/

@[expose] public noncomputable section PerfectDeltaResidueTensorTransport

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

end PerfectDeltaResidueTensorTransport
