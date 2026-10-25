import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensorPerfectoidUniversal
import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationTensorCompatibility
import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationCompletedTensorCompatibility
import SerrePositivity.BhattScholze.Perfectoidization.Prop813PerfectoidBaseChange
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Util.AssertNoSorry

/-! BS author-version Prop. 8.13: ring-valued universal properties and units.
This audit excludes the CLMST-D-owned Cor. 8.12 input.
-/

assert_no_sorry SerrePositivity.BhattScholze.existsUnique_completedTensorPerfectoidLift
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoid_hom_ext
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidLift
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidLift_comp
assert_no_sorry SerrePositivity.BhattScholze.completedTensorPerfectoidLift_isPerfectoidization

#print axioms SerrePositivity.BhattScholze.existsUnique_completedTensorPerfectoidLift
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoid_hom_ext
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidLift
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidLift_comp
#print axioms SerrePositivity.BhattScholze.completedTensorPerfectoidLift_isPerfectoidization

assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationTensorDiagramMap
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationTensorDiagramMap_tmul
assert_no_sorry SerrePositivity.BhattScholze.perfectoidizationTensorDiagramMap_isPerfectoidization

#print axioms SerrePositivity.BhattScholze.perfectoidizationTensorDiagramMap
#print axioms SerrePositivity.BhattScholze.perfectoidizationTensorDiagramMap_tmul
#print axioms SerrePositivity.BhattScholze.perfectoidizationTensorDiagramMap_isPerfectoidization

assert_no_sorry SerrePositivity.BhattScholze.prop813TensorMap
assert_no_sorry SerrePositivity.BhattScholze.prop813TensorMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.prop813CompletedTensorMap
assert_no_sorry SerrePositivity.BhattScholze.prop813CompletedTensorMap_comp_unit
assert_no_sorry SerrePositivity.BhattScholze.prop813CompletedTensorMap_unit_tmul
assert_no_sorry SerrePositivity.BhattScholze.prop813CompletedTensorMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.prop813_perfectoidTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.prop813ComparisonEquiv
assert_no_sorry SerrePositivity.BhattScholze.prop813ComparisonEquiv_comp
assert_no_sorry SerrePositivity.BhattScholze.prop813ComparisonEquiv_unique
assert_no_sorry SerrePositivity.BhattScholze.prop813ComparisonEquiv_symm_comp

#print axioms SerrePositivity.BhattScholze.prop813TensorMap
#print axioms SerrePositivity.BhattScholze.prop813TensorMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.prop813CompletedTensorMap
#print axioms SerrePositivity.BhattScholze.prop813CompletedTensorMap_comp_unit
#print axioms SerrePositivity.BhattScholze.prop813CompletedTensorMap_unit_tmul
#print axioms SerrePositivity.BhattScholze.prop813CompletedTensorMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.prop813_perfectoidTensor_pure
#print axioms SerrePositivity.BhattScholze.prop813ComparisonEquiv
#print axioms SerrePositivity.BhattScholze.prop813ComparisonEquiv_comp
#print axioms SerrePositivity.BhattScholze.prop813ComparisonEquiv_unique
#print axioms SerrePositivity.BhattScholze.prop813ComparisonEquiv_symm_comp

assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChangeMap
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChangeMap_comp_unit
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChangeMap_unit_tmul
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChangeMap_isPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChangeMap_left
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChange_exists_algEquiv
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChange_exists_algEquiv_of_tensor
assert_no_sorry SerrePositivity.BhattScholze.prop813BaseChange_exists_linearEquiv
assert_no_sorry SerrePositivity.BhattScholze.exists_prop813BaseChange_of_perfectoid_quotient
assert_no_sorry SerrePositivity.BhattScholze.exists_prop813BaseChange_of_semiperfectoid_quotient

#print axioms SerrePositivity.BhattScholze.prop813BaseChangeMap
#print axioms SerrePositivity.BhattScholze.prop813BaseChangeMap_comp_unit
#print axioms SerrePositivity.BhattScholze.prop813BaseChangeMap_unit_tmul
#print axioms SerrePositivity.BhattScholze.prop813BaseChangeMap_isPerfectoidization
#print axioms SerrePositivity.BhattScholze.prop813BaseChangeMap_left
#print axioms SerrePositivity.BhattScholze.prop813BaseChange_exists_algEquiv
#print axioms SerrePositivity.BhattScholze.prop813BaseChange_exists_algEquiv_of_tensor
#print axioms SerrePositivity.BhattScholze.prop813BaseChange_exists_linearEquiv
#print axioms SerrePositivity.BhattScholze.exists_prop813BaseChange_of_perfectoid_quotient
#print axioms SerrePositivity.BhattScholze.exists_prop813BaseChange_of_semiperfectoid_quotient

namespace BSProp813Audit
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private lemma identityPerfectoidization (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] (hA : IsIntegralPerfectoid A p) :
    IsPerfectoidization p (RingHom.id A) := by
  refine ⟨hA, ?_⟩
  intro U _ _ f
  exact ⟨f, RingHom.comp_id f, fun g hg => (RingHom.comp_id g).symm.trans hg⟩

-- Normalization of the actual comparison, including its noncomputable extension:
-- identity perfectoidizations induce the identity on the original completed H⁰.
lemma identity_normalization (p : ℕ) [Fact p.Prime]
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    prop813CompletedTensorMap p (RingHom.id R) (RingHom.id S) (RingHom.id T)
      (fun _ => rfl) (fun _ => rfl) (identityPerfectoidization p R hR)
      (identityPerfectoidization p S hS) (identityPerfectoidization p T hT) = RingHom.id _ := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  apply completedTensorPerfectoid_hom_ext R p S T _
    (integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR hS hT)
  apply RingHom.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y => ?_) (fun x y hx hy => ?_)
  · simpa only [RingHom.comp_apply, RingHom.id_apply] using
      prop813CompletedTensorMap_unit_tmul p (RingHom.id R) (RingHom.id S) (RingHom.id T)
        (fun _ => rfl) (fun _ => rfl) (identityPerfectoidization p R hR)
        (identityPerfectoidization p S hS) (identityPerfectoidization p T hT) x y
  · simp only [map_add, hx, hy]

-- No compatibility assumption beyond the original three perfectoidizations:
-- the existing functor supplies both maps from the perfectoidized base.
lemma canonical_diagram (p : ℕ) [Fact p.Prime]
    (R S T P C D : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing P] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R T]
    (r : R →+* P) (s : S →+* C) (t : T →+* D)
    (hr : IsPerfectoidization p r) (hs : IsPerfectoidization p s)
    (ht : IsPerfectoidization p t) :
    letI : Algebra P C := (hr.map hs (algebraMap R S)).toAlgebra
    letI : Algebra P D := (hr.map ht (algebraMap R T)).toAlgebra
    ∃ (hsc : ∀ x, s (algebraMap R S x) = algebraMap P C (r x))
      (htc : ∀ x, t (algebraMap R T x) = algebraMap P D (r x)),
      letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
      letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra P (p : P) C D)
      IsPerfectoidization p (prop813CompletedTensorMap p r s t hsc htc hr hs ht) := by
  let : Algebra P C := (hr.map hs (algebraMap R S)).toAlgebra
  let : Algebra P D := (hr.map ht (algebraMap R T)).toAlgebra
  have hsc (x : R) : s (algebraMap R S x) = algebraMap P C (r x) :=
    (RingHom.congr_fun (hr.map_comp hs (algebraMap R S)) x).symm
  have htc (x : R) : t (algebraMap R T x) = algebraMap P D (r x) :=
    (RingHom.congr_fun (hr.map_comp ht (algebraMap R T)) x).symm
  exact ⟨hsc, htc, prop813CompletedTensorMap_isPerfectoidization p r s t hsc htc hr hs ht⟩

-- A genuine zero-ring instance exercises both H⁰ ring structures and the new-base algebra.
lemma zero_base_change (p : ℕ) [Fact p.Prime] :
    let R := PUnit
    let hR : IsIntegralPerfectoid R p := Or.inl inferInstance
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) R R)
    IsPerfectoidization p
      (prop813BaseChangeMap R p R R R hR hR (AlgHom.id R R)
        (identityPerfectoidization p R hR)) := by
  exact prop813BaseChangeMap_isPerfectoidization PUnit p PUnit PUnit PUnit
    (Or.inl inferInstance) (Or.inl inferInstance) (AlgHom.id PUnit PUnit)
    (identityPerfectoidization p PUnit (Or.inl inferInstance))

assert_no_sorry identity_normalization
assert_no_sorry canonical_diagram
assert_no_sorry zero_base_change
#print axioms identity_normalization
#print axioms canonical_diagram
#print axioms zero_base_change

end BSProp813Audit
