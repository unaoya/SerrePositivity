module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTensorCoherence
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAlgebraAugmentation

/-! # Canonical completion of actual commutative derived algebra objects -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Complete actual commutative algebra objects using the proved canonical lax structure. -/
def boundedAboveCompletionCommMonFunctor : CommMon D ⥤ CommMon D := by
  letI := boundedAboveDerivedCompletionLaxBraided R a
  exact (boundedAboveDerivedCompletionFunctor R a).mapCommMon

/-- The completed algebra unit uses the original standard completion unit. -/
theorem boundedAboveCompletionCommMonFunctor_one (A : CommMon D) :
    ((boundedAboveCompletionCommMonFunctor R a).obj A).mon.one =
      (boundedAboveDerivedCompletionUnit R a).app (𝟙_ D) ≫
        (boundedAboveDerivedCompletionFunctor R a).map A.mon.one := rfl

/-- The standard completion unit itself is a morphism of actual commutative algebra objects. -/
def boundedAboveCompletionAlgebraUnit (A : CommMon D) :
    A ⟶ (boundedAboveCompletionCommMonFunctor R a).obj A := by
  letI := boundedAboveDerivedCompletionLaxBraided R a
  letI : NatTrans.IsMonoidal (boundedAboveDerivedCompletionUnit R a) :=
    boundedAboveDerivedCompletionUnitMonoidal R a
  exact (Functor.mapCommMonIdIso (C := D)).inv.app A ≫
    (Functor.mapCommMonNatTrans (boundedAboveDerivedCompletionUnit R a)).app A

/-- Forgetting the algebra structure recovers the existing standard unit exactly. -/
theorem boundedAboveCompletionAlgebraUnit_hom (A : CommMon D) :
    (boundedAboveCompletionAlgebraUnit R a A).hom.hom =
      (boundedAboveDerivedCompletionUnit R a).app A.X := by
  change 𝟙 A.X ≫ (boundedAboveDerivedCompletionUnit R a).app A.X = _
  exact Category.id_comp _

/-- Completion on algebra morphisms uses the original derived completion map. -/
theorem boundedAboveCompletionCommMonFunctor_map_hom {A B : CommMon D} (f : A ⟶ B) :
    ((boundedAboveCompletionCommMonFunctor R a).map f).hom.hom =
      (boundedAboveDerivedCompletionFunctor R a).map f.hom.hom := rfl

/-- The standard algebra completion unit is natural in all algebra morphisms. -/
theorem boundedAboveCompletionAlgebraUnit_naturality {A B : CommMon D} (f : A ⟶ B) :
    f ≫ boundedAboveCompletionAlgebraUnit R a B =
      boundedAboveCompletionAlgebraUnit R a A ≫
        (boundedAboveCompletionCommMonFunctor R a).map f := by
  apply CommMon.hom_ext
  change f.hom.hom ≫ (boundedAboveCompletionAlgebraUnit R a B).hom.hom =
    (boundedAboveCompletionAlgebraUnit R a A).hom.hom ≫
      ((boundedAboveCompletionCommMonFunctor R a).map f).hom.hom
  rw [boundedAboveCompletionAlgebraUnit_hom, boundedAboveCompletionAlgebraUnit_hom,
    boundedAboveCompletionCommMonFunctor_map_hom]
  exact (boundedAboveDerivedCompletionUnit R a).naturality f.hom.hom

/-- The actual completed derived tensor, with its canonical commutative algebra structure. -/
def boundedAboveCompletedTensorAlgebra
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] : CommMon D :=
  (boundedAboveCompletionCommMonFunctor R a).obj (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- The standard left factor map into the completed tensor is an algebra morphism. -/
def boundedAboveCompletedTensorAlgebraLeft
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedAlgebra (R := R) S ⟶ boundedAboveCompletedTensorAlgebra R a S T :=
  boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫
    boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- The standard right factor map into the completed tensor is an algebra morphism. -/
def boundedAboveCompletedTensorAlgebraRight
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedAlgebra (R := R) T ⟶ boundedAboveCompletedTensorAlgebra R a S T :=
  boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫
    boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- The completed actual standard augmentation is a commutative algebra morphism. -/
def boundedAboveCompletedTensorAlgebraAugmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletedTensorAlgebra R a S T ⟶
      (boundedAboveCompletionCommMonFunctor R a).obj
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) :=
  (boundedAboveCompletionCommMonFunctor R a).map
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T)

/-- The original standard augmentation diagram remains an algebra diagram after completion. -/
theorem boundedAboveCompletedTensorAlgebraAugmentation_unit
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra (R := R) S T) ≫
        boundedAboveCompletedTensorAlgebraAugmentation R a S T =
      boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T ≫
        boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) :=
  (boundedAboveCompletionAlgebraUnit_naturality R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T)).symm

/-- The left factor agrees with the ordinary tensor inclusion after completed augmentation. -/
theorem boundedAboveCompletedTensorAlgebraLeft_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletedTensorAlgebraLeft R a S T ≫
        boundedAboveCompletedTensorAlgebraAugmentation R a S T =
      boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) ≫
        boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) := by
  rw [boundedAboveCompletedTensorAlgebraLeft, Category.assoc,
    boundedAboveCompletedTensorAlgebraAugmentation_unit, ← Category.assoc,
    boundedAboveDerivedTensorAlgebraLeft_augmentation]

/-- The right factor agrees with the ordinary tensor inclusion after completed augmentation. -/
theorem boundedAboveCompletedTensorAlgebraRight_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletedTensorAlgebraRight R a S T ≫
        boundedAboveCompletedTensorAlgebraAugmentation R a S T =
      boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) ≫
        boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) := by
  rw [boundedAboveCompletedTensorAlgebraRight, Category.assoc,
    boundedAboveCompletedTensorAlgebraAugmentation_unit, ← Category.assoc,
    boundedAboveDerivedTensorAlgebraRight_augmentation]

end SerrePositivity.DerivedCompletion
