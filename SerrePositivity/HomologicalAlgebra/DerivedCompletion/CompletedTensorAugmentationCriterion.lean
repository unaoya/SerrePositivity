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

end SerrePositivity.DerivedCompletion
