module

public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationTensorCompatibility

/-! # BS Proposition 8.13 in the ring-valued reflection domain

For any compatible diagram of three specified ring-perfectoidizations, the
original completed tensor of the perfectoid rings is discrete and perfectoid.
Its actual H⁰ is the ring-perfectoidization of the actual original completed
tensor H⁰. The comparison preserves the original units and both factor maps.

The author-version proposition, pp. 69–70, concerns arbitrary derived p-complete
simplicial rings over a perfectoid ring and their derived E∞ perfectoidizations.
Here the ring-perfectoidizations are specified, rather than presumed to exist
for all rings. No identification of an arbitrary derived tensor with its H⁰ is
made. The proof uses the existing G2 comparison and the ring universal property
instead of the original argument via symmetric monoidal prismatic cohomology.
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] {R S T P C D : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing P] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R T] [Algebra P C] [Algebra P D]
    (r : R →+* P) (s : S →+* C) (t : T →+* D)
    (hs : ∀ x, s (algebraMap R S x) = algebraMap P C (r x))
    (ht : ∀ x, t (algebraMap R T x) = algebraMap P D (r x))
local notation "X" => boundedAboveCompletedTensorAlgebra R (p : R) S T
local notation "Y" => boundedAboveCompletedTensorAlgebra P (p : P) C D
set_option quotPrecheck false in
local notation "HX" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (X).X.obj
set_option quotPrecheck false in
local notation "HY" => (DerivedCategory.homologyFunctor (ModuleCat P) 0).obj (Y).X.obj

/-- The original tensor unit followed by the original completed target unit. -/
def prop813TensorMap :
    letI := derivedH0CommRing Y
    S ⊗[R] T →+* HY := by
  letI := derivedH0CommRing Y
  exact (completedTensorPerfectoidizationMap P p C D).comp
    (perfectoidizationTensorDiagramMap r s t hs ht)

/-- The specified completed perfectoid tensor is the universal perfectoid target
of the original ordinary tensor diagram. -/
lemma prop813TensorMap_isPerfectoidization
    (hr : IsPerfectoidization p r) (hsp : IsPerfectoidization p s)
    (htp : IsPerfectoidization p t) :
    letI := derivedH0CommRing Y
    IsPerfectoidization p (prop813TensorMap p r s t hs ht) := by
  let := derivedH0CommRing Y
  exact perfectoidizationTensorDiagramMap_isPerfectoidization r s t hs ht p hr hsp htp _
    (completedTensorPerfectoidizationMap P p C D)
    (completedTensorPerfectoidizationMap_isPerfectoidization P p C D hr.1 hsp.1 htp.1)

variable (hr : IsPerfectoidization p r) (hsp : IsPerfectoidization p s)
    (htp : IsPerfectoidization p t)

/-- Extend the specified tensor diagram over its original actual H⁰ completion unit. -/
def prop813CompletedTensorMap :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    HX →+* HY := by
  letI := derivedH0CommRing X
  letI := derivedH0CommRing Y
  exact completedTensorPerfectoidLift R p S T _
    (prop813TensorMap_isPerfectoidization p r s t hs ht hr hsp htp).1
    (prop813TensorMap p r s t hs ht)

/-- The map commutes with the original completion-unit square. -/
lemma prop813CompletedTensorMap_comp_unit :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    (prop813CompletedTensorMap p r s t hs ht hr hsp htp).comp
      (completedTensorPerfectoidizationMap R p S T) = prop813TensorMap p r s t hs ht := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_comp R p S T _ _ _

/-- Both original factor maps are retained on each pure tensor class. -/
lemma prop813CompletedTensorMap_unit_tmul (x : S) (y : T) :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    prop813CompletedTensorMap p r s t hs ht hr hsp htp
      (completedTensorPerfectoidizationMap R p S T (x ⊗ₜ[R] y)) =
        completedTensorPerfectoidizationMap P p C D (s x ⊗ₜ[P] t y) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  have h := RingHom.congr_fun
    (prop813CompletedTensorMap_comp_unit p r s t hs ht hr hsp htp) (x ⊗ₜ[R] y)
  change _ = completedTensorPerfectoidizationMap P p C D
    (perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] y)) at h
  simpa only [RingHom.comp_apply, perfectoidizationTensorDiagramMap_tmul] using h

/-- Ring form of BS Prop. 8.13: the same actual completed perfectoid tensor H⁰
is the universal perfectoidization of the original completed tensor H⁰. -/
lemma prop813CompletedTensorMap_isPerfectoidization :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    IsPerfectoidization p (prop813CompletedTensorMap p r s t hs ht hr hsp htp) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_isPerfectoidization R p S T _ _
    (prop813TensorMap_isPerfectoidization p r s t hs ht hr hsp htp)

omit [Algebra R S] [Algebra R T] in
include hr hsp htp in
/-- The perfectoidized tensor in this statement is the original discrete
completed derived tensor, not a replacement chosen only at the level of H⁰. -/
lemma prop813_perfectoidTensor_pure : (Y).X.obj.IsGE 0 ∧ (Y).X.obj.IsLE 0 :=
  integralPerfectoid_completedTensor_pure p P C D hr.1 hsp.1 htp.1

/-- The standard comparison with any specified ring-perfectoidization of the
original completed tensor. Its orientation is the one in BS Prop. 8.13. -/
def prop813ComparisonEquiv (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E), IsPerfectoidization p g → HY ≃+* E := by
  letI := derivedH0CommRing X
  letI := derivedH0CommRing Y
  intro g hg
  exact ((prop813CompletedTensorMap_isPerfectoidization p r s t hs ht hr hsp htp).exists_equiv
    p hg).choose

/-- The comparison preserves the entire original completed-tensor map. -/
lemma prop813ComparisonEquiv_comp (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E) (hg : IsPerfectoidization p g),
      (prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg).toRingHom.comp
        (prop813CompletedTensorMap p r s t hs ht hr hsp htp) = g := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  intro g hg
  exact ((prop813CompletedTensorMap_isPerfectoidization p r s t hs ht hr hsp htp).exists_equiv
    p hg).choose_spec

/-- A comparison retaining the original unit is unique, so the equivalence does
not depend on an additional choice of comparison map. -/
lemma prop813ComparisonEquiv_unique (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E) (hg : IsPerfectoidization p g) (f : HY →+* E),
      f.comp (prop813CompletedTensorMap p r s t hs ht hr hsp htp) = g →
        f = (prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg).toRingHom := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  intro g hg f hf
  exact ((prop813CompletedTensorMap_isPerfectoidization p r s t hs ht hr hsp htp).2 E hg.1 g).unique
    hf (prop813ComparisonEquiv_comp p r s t hs ht hr hsp htp E g hg)

/-- The inverse comparison also retains the entire original completed-tensor map. -/
lemma prop813ComparisonEquiv_symm_comp (E : Type u) [CommRing E] :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    ∀ (g : HX →+* E) (hg : IsPerfectoidization p g),
      (prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg).symm.toRingHom.comp g =
        prop813CompletedTensorMap p r s t hs ht hr hsp htp := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  intro g hg
  let e := prop813ComparisonEquiv p r s t hs ht hr hsp htp E g hg
  apply RingHom.ext
  intro x
  apply e.injective
  change e (e.symm (g x)) = e (prop813CompletedTensorMap p r s t hs ht hr hsp htp x)
  rw [e.apply_symm_apply]
  exact (RingHom.congr_fun
    (prop813ComparisonEquiv_comp p r s t hs ht hr hsp htp E g hg) x).symm

end SerrePositivity.BhattScholze
