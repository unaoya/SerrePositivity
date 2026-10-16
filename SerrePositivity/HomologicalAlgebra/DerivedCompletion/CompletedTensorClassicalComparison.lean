module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorH0Comparison
/-! # The actual completed tensor H0 and the classical completion of the ordinary tensor

The standard G2 augmentation and F3 comparison are composed with the regular
principal completion comparison. The original unit and both factor maps are retained.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hB : IsSMulRegular (S ⊗[R] T) (p : S ⊗[R] T))
local notation "B" => S ⊗[R] T

/-- Compare the original H0 ring with the classical completion of the ordinary tensor. -/
def completedTensorH0AdicRingEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
        AdicCompletion (Ideal.span {(p : B)}) B := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing B p 0
  letI := pdCompletionBaseAlgebra R B p 0
  letI := pairCompletionAlgebra B (p : B) 0
  letI := principalCompletionCommRing B (p : B)
  letI := principalCompletionAlgebra B (p : B)
  exact (completedTensorH0PDAlgEquiv R p S T).toRingEquiv.trans
    ((pairCompletionZeroPrincipalAlgEquiv B (p : B)).toRingEquiv.trans
      (principalCompletionAdicAlgEquiv B (p : B) hB).toRingEquiv)

/-- The ring comparison preserves the original completion unit. -/
lemma completedTensorH0AdicRingEquiv_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B) (derivedTensorH0AlgEquiv S T x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T _)) = _
  rw [completedTensorH0PDAlgEquiv_unit]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 _)) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]

/-- The original left factor map becomes the standard completed tensor inclusion. -/
lemma completedTensorH0AdicRingEquiv_left
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T) x) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T _)) = _
  rw [completedTensorH0PDAlgEquiv_left]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 _)) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]

/-- The original right factor map becomes the standard completed tensor inclusion. -/
lemma completedTensorH0AdicRingEquiv_right
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T) x) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] B)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R T) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T _)) = _
  rw [completedTensorH0PDAlgEquiv_right]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 _)) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]

/-- The comparison preserves the original coefficient algebra map. -/
lemma completedTensorH0AdicRingEquiv_algebraMap (r : R) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB (algebraMap R _ r) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B) (algebraMap R B r) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T (algebraMap R _ r))) = _
  rw [(completedTensorH0PDAlgEquiv R p S T).commutes]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 (algebraMap R B r))) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]
end SerrePositivity.DerivedCompletion
