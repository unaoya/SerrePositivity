module
public import SerrePositivity.BhattScholze.Prism.PerfectDeltaCartierTensorAlgebra
public import SerrePositivity.BhattScholze.Prism.PerfectDeltaCartierTensorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorCartierProducts

/-! # The actual perfect-prism Cartier tensor comparison as an algebra isomorphism -/
@[expose] public noncomputable section
universe u
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
