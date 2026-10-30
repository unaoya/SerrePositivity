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
