module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraPDComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorAugmentationCriterion

/-! # The actual completed tensor H⁰ and the original F3 algebra of the ordinary tensor -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ)
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The original completed augmentation supplies an F3 algebra comparison whenever invertible. -/
def completedTensorH0PDAlgEquivOfIso
    (h : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T).hom.hom) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := derivedH0CommRing (completedAlgebra R (p : R) (S ⊗[R] T))
  letI := derivedH0Algebra (completedAlgebra R (p : R) (S ⊗[R] T))
  exact (derivedH0AlgEquivOfIsoUnderlying
    (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T) h).trans
      (completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p)

/-- Its function is the actual completed augmentation followed by the standard F3 comparison. -/
lemma completedTensorH0PDAlgEquivOfIso_apply
    (h : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T).hom.hom)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquivOfIso R p S T h x =
      completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T) x) := rfl

/-- The comparison preserves the completion unit and the original ordinary tensor H⁰ class. -/
lemma completedTensorH0PDAlgEquivOfIso_unit
    (h : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T).hom.hom)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquivOfIso R p S T h
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      pdCompletionUnit (S ⊗[R] T) p 0 (derivedTensorH0AlgEquiv S T x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [completedTensorH0PDAlgEquivOfIso_apply, completedTensorH0AlgebraAugmentation_unit]
  have hb : completedAlgebraUnitAlgHom R (p : R) (S ⊗[R] T)
      (derivedTensorH0AlgEquiv S T x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x) := by
    rw [completedAlgebraUnitAlgHom_apply]
    have hz : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R (S ⊗[R] T)) (derivedTensorH0AlgEquiv S T x) =
        derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x := by
      change (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R (S ⊗[R] T))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
          (ModuleCat.of R (S ⊗[R] T))
          (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x)) = _
      exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
        (ModuleCat.of R (S ⊗[R] T))).toLinearEquiv.symm_apply_apply _
    rw [hz]
  rw [← hb, completedAlgebraH0PDAlgEquiv_unit]

/-- The left factor keeps its original ordinary tensor inclusion in F3. -/
lemma completedTensorH0PDAlgEquivOfIso_left
    (h : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T).hom.hom)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquivOfIso R p S T h
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T) x) =
      pdCompletionUnit (S ⊗[R] T) p 0
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [boundedAboveCompletedTensorAlgebraLeft, ← derivedH0AlgMap_comp_apply]
  erw [completedTensorH0PDAlgEquivOfIso_unit R p S T h]
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_left]

/-- The right factor keeps its original ordinary tensor inclusion in F3. -/
lemma completedTensorH0PDAlgEquivOfIso_right
    (h : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T).hom.hom)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquivOfIso R p S T h
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T) x) =
      pdCompletionUnit (S ⊗[R] T) p 0
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R T) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [boundedAboveCompletedTensorAlgebraRight, ← derivedH0AlgMap_comp_apply]
  erw [completedTensorH0PDAlgEquivOfIso_unit R p S T h]
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_right]

/-- All higher Tor vanishing supplies the original F3 comparison before completion. -/
def completedTensorH0PDAlgEquivOfTor
    (hTor : ∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T))) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 :=
  completedTensorH0PDAlgEquivOfIso R p S T
    (completedTensorAlgebraAugmentation_isIso_of_tor R (p : R) S T hTor)

/-- Alternatively use the exact all-power Koszul criterion after completion. -/
def completedTensorH0PDAlgEquivOfKoszul
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R ((p : R) ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom)) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 :=
  completedTensorH0PDAlgEquivOfIso R p S T
    ((completedTensorAlgebraAugmentation_isIso_iff_koszul R (p : R) S T).mpr hKos)

end SerrePositivity.DerivedCompletion
