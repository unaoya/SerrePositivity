module
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectDeltaCompletedTensorH0
public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDPrism
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismQuotientPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorH0Complete

/-! # Perfect delta structure and prism on original iterated completed tensor H⁰

The original H⁰ ring, base action and second completion unit are retained.
Discreteness of the second derived object and its Cartier quotient comparison
are separate subsequent steps.
-/
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
