module
public import SerrePositivity.BhattScholze.PerfectDeltaIteratedTensorH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularCompletionPure

/-! # Discreteness of the original p,d completed tensor of perfect delta rings -/
@[expose] public noncomputable section
universe u
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
