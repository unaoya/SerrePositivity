module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorPDComparison

/-! # Unconditional actual H0 comparison for the completed tensor augmentation -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Invertibility of the actual H0 map suffices for an H0 algebra equivalence. -/
def derivedH0AlgEquivOfIsoHomology
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))} (f : A ⟶ B)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f.hom.hom.hom)) :
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ≃ₐ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj := by
  letI := derivedH0CommRing A
  letI := derivedH0CommRing B
  letI := derivedH0Algebra A
  letI := derivedH0Algebra B
  have := hf
  have hb := ConcreteCategory.bijective_of_isIso
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom)
  refine AlgEquiv.ofBijective (derivedH0AlgMap f) ?_
  change Function.Bijective (fun x :
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ↦
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x) at hb
  simpa only [← derivedH0AlgMap_apply] using hb

namespace DerivedCompletion
variable (R) (a : R)

/-- The standard completed augmentation is always invertible on actual H0.
This does not assert invertibility on other cohomology degrees. -/
lemma completedTensorAlgebraAugmentation_h0_isIso
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom.hom) := by
  apply boundedAboveDerivedCompletion_h0_map_isIso R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom
  · change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R S)).obj
      (ModuleCat.of R T)).IsLE 0
    infer_instance
  · change ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (S ⊗[R] T))).IsLE 0
    infer_instance
  · rw [boundedAboveDerivedTensorAlgebraAugmentation_hom]
    exact derivedTensorAugmentation_h0_isIso (ModuleCat.of R S) (ModuleCat.of R T)

variable (p : ℕ) (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The original completed augmentation gives the F3 comparison without Tor or Koszul hypotheses. -/
def completedTensorH0PDAlgEquiv :
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
  exact (derivedH0AlgEquivOfIsoHomology
    (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T)
    (completedTensorAlgebraAugmentation_h0_isIso R (p : R) S T)).trans
      (completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p)

/-- Its function is the actual completed augmentation followed by the standard F3 comparison. -/
lemma completedTensorH0PDAlgEquiv_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T x =
      completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T) x) := rfl

/-- The comparison preserves the completion unit and the original ordinary tensor H⁰ class. -/
lemma completedTensorH0PDAlgEquiv_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      pdCompletionUnit (S ⊗[R] T) p 0 (derivedTensorH0AlgEquiv S T x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [completedTensorH0PDAlgEquiv_apply, completedTensorH0AlgebraAugmentation_unit]
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
lemma completedTensorH0PDAlgEquiv_left
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T
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
  erw [completedTensorH0PDAlgEquiv_unit R p S T]
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_left]

/-- The right factor keeps its original ordinary tensor inclusion in F3. -/
lemma completedTensorH0PDAlgEquiv_right
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T
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
  erw [completedTensorH0PDAlgEquiv_unit R p S T]
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_right]

end DerivedCompletion
end SerrePositivity
