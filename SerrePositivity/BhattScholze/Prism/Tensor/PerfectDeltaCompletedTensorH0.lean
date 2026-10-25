module

public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectDeltaTensorPCompletion
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaTransport
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorClassicalComparison
/-! # A perfect delta structure on the original completed derived tensor H0

The original H0 ring is compared with the classical completion preserving the
unit, coefficient map, and factor maps. The perfect delta structure is transported
through that exact ring equivalence. The subsequent d-completion is separate.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- Transport of a perfect delta structure through a ring equivalence stays perfect. -/
lemma DeltaStructure.IsPerfect.comapEquiv {p : ℕ} [Fact p.Prime]
    {X Y : Type u} [CommRing X] [CommRing Y] {E : DeltaStructure p Y}
    (hE : E.IsPerfect) (e : X ≃+* Y) : (E.comapEquiv e).IsPerfect := by
  have he := E.comapEquiv_isDeltaHom e
  have hf (x : X) : e ((E.comapEquiv e).frobeniusLift x) = E.frobeniusLift (e x) :=
    he.map_frobeniusLift x
  constructor
  · intro x y hxy
    apply e.injective
    apply hE.injective
    rw [← hf, ← hf, hxy]
  · intro x
    obtain ⟨y, hy⟩ := hE.surjective (e x)
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [hf, e.apply_symm_apply, hy]

variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))
local notation "B" => S ⊗[R] T
local notation "Cp" => AdicCompletion (Ideal.span {(p : B)}) B
-- This carrier notation contains functor projections; only its syntax precheck is disabled.
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj

/-- The original completed tensor H0 receives the transported delta structure. -/
def perfectDeltaCompletedTensorH0Structure :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DeltaStructure p H := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).comapEquiv
    (completedTensorH0AdicRingEquiv R p S T
      (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT))

/-- The delta structure on the actual H0 ring is perfect. -/
lemma perfectDeltaCompletedTensorH0Structure_isPerfect :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaTensorPCompletionStructure_isPerfect p R S T DR DS DT hR hS hT hRS hRT).comapEquiv
    (completedTensorH0AdicRingEquiv R p S T
      (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT))

/-- The standard comparison with classical completion preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom
      (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0AdicRingEquiv R p S T
        (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)).toRingHom := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).comapEquiv_isDeltaHom
    (completedTensorH0AdicRingEquiv R p S T
      (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT))

/-- The original left factor map on actual H0, normalized by the standard single comparison. -/
def completedTensorH0LeftRingHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    S →+* H := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃+* S :=
    derivedSingleH0RingEquiv (R := R) S
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T)).toRingHom.comp
    eS.symm.toRingHom

/-- The original right factor map on actual H0, normalized by the standard single comparison. -/
def completedTensorH0RightRingHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    T →+* H := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃+* T :=
    derivedSingleH0RingEquiv (R := R) T
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T)).toRingHom.comp
    eT.symm.toRingHom


omit [Fact p.Prime] in
/-- The original left factor map agrees with the classical completed inclusion. -/
lemma completedTensorH0LeftRingHom_comparison
    (hB : IsSMulRegular B (p : B)) (x : S) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB (completedTensorH0LeftRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃+* S :=
    derivedSingleH0RingEquiv (R := R) S
  change completedTensorH0AdicRingEquiv R p S T hB
    (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T)
      (eS.symm x)) = _
  rw [completedTensorH0AdicRingEquiv_left]
  have hx : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
      (ModuleCat.of R S) (eS.symm x) = x :=
    eS.apply_symm_apply x
  rw [hx]

omit [Fact p.Prime] in
/-- The original right factor map agrees with the classical completed inclusion. -/
lemma completedTensorH0RightRingHom_comparison
    (hB : IsSMulRegular B (p : B)) (x : T) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB (completedTensorH0RightRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃+* T :=
    derivedSingleH0RingEquiv (R := R) T
  change completedTensorH0AdicRingEquiv R p S T hB
    (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T)
      (eT.symm x)) = _
  rw [completedTensorH0AdicRingEquiv_right]
  have hx : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
      (ModuleCat.of R T) (eT.symm x) = x :=
    eT.apply_symm_apply x
  rw [hx]

/-- The original left factor map preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_includeLeft_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DS.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0LeftRingHom p R S T) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let e := completedTensorH0AdicRingEquiv R p S T
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  let DH := perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
  let DC := perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT
  have he := perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hf := perfectDeltaTensorPCompletionStructure_includeLeft_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hx (x : S) : e (completedTensorH0LeftRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) x) :=
    completedTensorH0LeftRingHom_comparison p R S T _ x
  change DS.IsDeltaHom DH (completedTensorH0LeftRingHom p R S T)
  intro x
  apply e.injective
  calc
    _ = algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) (DS.delta x)) := hx _
    _ = DC.delta (algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) x)) := hf x
    _ = DC.delta (e (completedTensorH0LeftRingHom p R S T x)) := congrArg DC.delta (hx x).symm
    _ = _ := (he _).symm

/-- The original right factor map preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_includeRight_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DT.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0RightRingHom p R S T) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let e := completedTensorH0AdicRingEquiv R p S T
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  let DH := perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
  let DC := perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT
  have he := perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hf := perfectDeltaTensorPCompletionStructure_includeRight_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hx (x : T) : e (completedTensorH0RightRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) x) :=
    completedTensorH0RightRingHom_comparison p R S T _ x
  change DT.IsDeltaHom DH (completedTensorH0RightRingHom p R S T)
  intro x
  apply e.injective
  calc
    _ = algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) (DT.delta x)) := hx _
    _ = DC.delta (algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) x)) := hf x
    _ = DC.delta (e (completedTensorH0RightRingHom p R S T x)) := congrArg DC.delta (hx x).symm
    _ = _ := (he _).symm

/-- The original H0 coefficient algebra map preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_base_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DR.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap R H) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let e := completedTensorH0AdicRingEquiv R p S T
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  let DH := perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
  let DC := perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT
  have he := perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hf := perfectDeltaTensorPCompletionStructure_base_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hx (r : R) : e (algebraMap R H r) = algebraMap B Cp (algebraMap R B r) :=
    completedTensorH0AdicRingEquiv_algebraMap R p S T _ r
  change DR.IsDeltaHom DH (algebraMap R H)
  intro r
  apply e.injective
  calc
    _ = algebraMap B Cp (algebraMap R B (DR.delta r)) := hx _
    _ = DC.delta (algebraMap B Cp (algebraMap R B r)) := hf r
    _ = DC.delta (e (algebraMap R H r)) := congrArg DC.delta (hx r).symm
    _ = _ := (he _).symm

/-- The original p-completed tensor is discrete and its actual H0 delta structure is perfect. -/
lemma perfectDeltaCompletedTensor_discrete_perfect :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 ∧
        (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  have hpure := perfectDelta_completedTensor_pure p R S T DR DS DT hR hS hT
  exact ⟨hpure.1, hpure.2.1,
    perfectDeltaCompletedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT⟩

/-- A distinguished base element remains distinguished on actual H0. -/
lemma perfectDeltaCompletedTensorH0Structure_distinguished (d : R) (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsDistinguished
      (algebraMap R H d) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaCompletedTensorH0Structure_base_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT).map_isDistinguished hd

include hR hS hT hRS hRT in
/-- Its image is regular on actual H0, using the proved p-adic completeness. -/
lemma perfectDeltaCompletedTensorH0Structure_distinguished_regular
    (d : R) (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    Function.Injective (fun x : H => algebraMap R H d * x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  have : IsAdicComplete (Ideal.span {(p : H)}) H :=
    perfectDelta_completedTensorH0_isAdicComplete p R S T DR DS DT hR hS hT
  have hperf := perfectDeltaCompletedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT
  exact hperf.distinguished_mul_injective
      (perfectDeltaCompletedTensorH0Structure_distinguished p R S T DR DS DT hR hS hT hRS hRT d hd)
end SerrePositivity.BhattScholze
