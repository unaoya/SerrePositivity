module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationIso

/-! # An exact Koszul criterion for the completed standard tensor augmentation -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Completion inverts the original augmentation exactly when every power-Koszul reduction does. -/
lemma completedTensorAlgebraAugmentation_isIso_iff_koszul
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    IsIso (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom ↔
      ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
        (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom) := by
  have he : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom ↔
      IsIso ((derivedComplexCompletionFunctor R a).map
        (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom) := by
    constructor
    · intro h
      have := h
      exact inferInstanceAs (IsIso (DerivedCategory.Minus.ι.map
        (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom))
    · intro h
      have : IsIso (DerivedCategory.Minus.ι.map
          (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom) := h
      exact isIso_of_reflects_iso
        (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom DerivedCategory.Minus.ι
  exact he.trans (boundedAboveCompletion_map_isIso_iff_koszul R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom)

/-- Compare completed actual H⁰ algebras without requiring Tor vanishing before completion. -/
def completedTensorH0AlgEquivOfKoszul
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom)) :
    let A := boundedAboveCompletedTensorAlgebra R a S T
    let B := (boundedAboveCompletionCommMonFunctor R a).obj
      (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T))
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ≃ₐ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj :=
  derivedH0AlgEquivOfIsoUnderlying (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
    ((completedTensorAlgebraAugmentation_isIso_iff_koszul R a S T).mpr hKos)

/-- The comparison is the actual completed standard augmentation on H⁰. -/
lemma completedTensorH0AlgEquivOfKoszul_apply
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    completedTensorH0AlgEquivOfKoszul R a S T hKos x =
      derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T) x := rfl

/-- Even without precompletion Tor vanishing, the comparison preserves the original unit square. -/
lemma completedTensorH0AlgEquivOfKoszul_unit
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    completedTensorH0AlgEquivOfKoszul R a S T hKos
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x) := by
  rw [completedTensorH0AlgEquivOfKoszul_apply]
  exact completedTensorH0AlgebraAugmentation_unit R a S T x

/-- The completed left factor agrees with the ordinary inclusion under the Koszul comparison. -/
lemma completedTensorH0AlgEquivOfKoszul_left
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    completedTensorH0AlgEquivOfKoszul R a S T hKos
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)) x) := by
  rw [completedTensorH0AlgEquivOfKoszul_apply]
  exact completedTensorH0AlgebraLeft_augmentation R a S T x

/-- The completed right factor agrees with the ordinary inclusion under the Koszul comparison. -/
lemma completedTensorH0AlgEquivOfKoszul_right
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    completedTensorH0AlgEquivOfKoszul R a S T hKos
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R a S T) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)) x) := by
  rw [completedTensorH0AlgEquivOfKoszul_apply]
  exact completedTensorH0AlgebraRight_augmentation R a S T x

end SerrePositivity.DerivedCompletion
