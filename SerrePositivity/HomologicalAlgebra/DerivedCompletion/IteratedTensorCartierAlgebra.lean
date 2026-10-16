module
public import SerrePositivity.CommutativeAlgebra.MappedPrincipalQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0AlgebraUniversal
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

/-! # Original residue-factor algebra maps into the original iterated Cartier quotient -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX
/-- The original left factor map through both original completion units, on actual H⁰. -/
def iteratedTensorH0LeftAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    S →ₐ[R] C := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃ₐ[R] S :=
    derivedSingleH0AlgEquiv (R := R) S
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T ≫
    boundedAboveCompletionAlgebraUnit R d AP)).comp e.symm.toAlgHom

/-- The original left factor descends to the original ordinary residue ring over Q. -/
def iteratedTensorCartierLeftAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    SQ →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (principalAdicReductionAlgHom R d (iteratedTensorH0LeftAlgHom R a d S T)).comp
    (mappedPrincipalQuotientAlgEquiv R d S).toAlgHom

/-- The residue map retains the original representative and original factor action. -/
lemma iteratedTensorCartierLeftAlgHom_mk (x : S) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierLeftAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0LeftAlgHom R a d S T x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  change principalAdicReductionAlgHom R d (iteratedTensorH0LeftAlgHom R a d S T)
    (mappedPrincipalQuotientAlgEquiv R d S (Ideal.Quotient.mk _ x)) = _
  rw [mappedPrincipalQuotientAlgEquiv_mk, principalAdicReductionAlgHom_mk]

/-- The original right factor map through both original completion units, on actual H⁰. -/
def iteratedTensorH0RightAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    T →ₐ[R] C := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃ₐ[R] T :=
    derivedSingleH0AlgEquiv (R := R) T
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R a S T ≫
    boundedAboveCompletionAlgebraUnit R d AP)).comp e.symm.toAlgHom

/-- The original right factor descends to the original ordinary residue ring over Q. -/
def iteratedTensorCartierRightAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    TQ →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (principalAdicReductionAlgHom R d (iteratedTensorH0RightAlgHom R a d S T)).comp
    (mappedPrincipalQuotientAlgEquiv R d T).toAlgHom

/-- The residue map retains the original representative and original factor action. -/
lemma iteratedTensorCartierRightAlgHom_mk (x : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierRightAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0RightAlgHom R a d S T x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  change principalAdicReductionAlgHom R d (iteratedTensorH0RightAlgHom R a d S T)
    (mappedPrincipalQuotientAlgEquiv R d T (Ideal.Quotient.mk _ x)) = _
  rw [mappedPrincipalQuotientAlgEquiv_mk, principalAdicReductionAlgHom_mk]

/-- The ordinary residue tensor maps to the original Cartier quotient by its original factors. -/
def iteratedTensorCartierTensorAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    SQ ⊗[Q] TQ →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact Algebra.TensorProduct.lift (iteratedTensorCartierLeftAlgHom R a d S T)
    (iteratedTensorCartierRightAlgHom R a d S T) (fun _ _ => Commute.all _ _)

/-- Pure tensors of original representatives have their original product Cartier image. -/
lemma iteratedTensorCartierTensorAlgHom_tmul (s : S) (t : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierTensorAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
          Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d}) (iteratedTensorH0LeftAlgHom R a d S T s) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0RightAlgHom R a d S T t) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  simp only [iteratedTensorCartierTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [iteratedTensorCartierLeftAlgHom_mk, iteratedTensorCartierRightAlgHom_mk]


set_option maxHeartbeats 800000 in
-- Elaborating this map compares the original R-H⁰ ring and both Q-derived H⁰ algebra instances.
/-- The canonical extension to actual completed residue-tensor H⁰, for the same Cartier quotient. -/
def iteratedTensorCartierCompletedAlgHom
    (hp :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
  letI := derivedH0CommRing RX
  letI := derivedH0Algebra RX
  letI := derivedH0CommRing RC
  letI := derivedH0Algebra RC
  let hle : (RX).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of Q SQ)).obj
      (ModuleCat.of Q TQ)).IsLE 0
    infer_instance
  exact completionH0AlgebraLift Q ((q) a) RX CQ hp
    ((iteratedTensorCartierTensorAlgHom R a d S T).comp
      (derivedTensorH0AlgEquiv (R := Q) SQ TQ).toAlgHom)

/-- This algebra extension retains the original actual residue-tensor completion unit. -/
lemma iteratedTensorCartierCompletedAlgHom_unit
    (hp :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ))
    (x : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RX).X.obj) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    iteratedTensorCartierCompletedAlgHom R a d S T hp
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q ((q) a) RX) x) =
      iteratedTensorCartierTensorAlgHom R a d S T
        (derivedTensorH0AlgEquiv (R := Q) SQ TQ x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  let hle : (RX).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of Q SQ)).obj
      (ModuleCat.of Q TQ)).IsLE 0
    infer_instance
  have h := completionH0AlgebraLift_unit Q ((q) a) RX CQ hp
    ((iteratedTensorCartierTensorAlgHom R a d S T).comp
      (derivedTensorH0AlgEquiv (R := Q) SQ TQ).toAlgHom)
  exact congrArg (fun f => f x) h

end SerrePositivity.DerivedCompletion
