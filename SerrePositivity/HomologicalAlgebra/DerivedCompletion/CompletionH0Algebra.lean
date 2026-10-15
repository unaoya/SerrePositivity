module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-! # Actual H⁰ algebra diagrams for the original completion unit and tensor augmentation -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Evaluation of composition uses the original actual H⁰ maps. -/
lemma derivedH0AlgMap_comp_apply
    {A B C : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))}
    (f : A ⟶ B) (g : B ⟶ C)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap g (derivedH0AlgMap f x) = derivedH0AlgMap (f ≫ g) x := by
  rw [derivedH0AlgMap_apply, derivedH0AlgMap_apply, derivedH0AlgMap_apply]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map g.hom.hom.hom
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x) =
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map (f.hom.hom.hom ≫ g.hom.hom.hom) x
  rw [CategoryTheory.Functor.map_comp]
  rfl

namespace DerivedCompletion
variable (R) (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- The H⁰ algebra completion map is the H⁰ map of the original standard completion unit. -/
lemma completionH0AlgebraUnit_apply (A : CommMon D)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A) x =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionUnit R a).app A.X).hom x := by
  rw [derivedH0AlgMap_apply, boundedAboveCompletionAlgebraUnit_hom]
  rfl

/-- The actual H⁰ algebra completion maps satisfy the standard unit naturality square. -/
lemma completionH0AlgebraUnit_naturality {A B : CommMon D} (f : A ⟶ B)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap ((boundedAboveCompletionCommMonFunctor R a).map f)
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a B) (derivedH0AlgMap f x) := by
  rw [derivedH0AlgMap_comp_apply, derivedH0AlgMap_comp_apply,
    boundedAboveCompletionAlgebraUnit_naturality]

/-- The augmented completed tensor H⁰ uses the original completed augmentation map. -/
lemma completedTensorH0AlgebraAugmentation_apply
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T) x =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom).hom x := by
  rw [derivedH0AlgMap_apply]
  rfl

/-- The original augmentation and completion unit square commutes as actual H⁰ algebra maps. -/
lemma completedTensorH0AlgebraAugmentation_unit
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x) := by
  exact completionH0AlgebraUnit_naturality R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x

/-- The completed left factor agrees with the completed ordinary inclusion. -/
lemma completedTensorH0AlgebraLeft_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)) x) := by
  rw [derivedH0AlgMap_comp_apply, derivedH0AlgMap_comp_apply,
    boundedAboveCompletedTensorAlgebraLeft_augmentation]

/-- The completed right factor agrees with the completed ordinary inclusion. -/
lemma completedTensorH0AlgebraRight_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R a S T) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)) x) := by
  rw [derivedH0AlgMap_comp_apply, derivedH0AlgMap_comp_apply,
    boundedAboveCompletedTensorAlgebraRight_augmentation]

end DerivedCompletion
end SerrePositivity
