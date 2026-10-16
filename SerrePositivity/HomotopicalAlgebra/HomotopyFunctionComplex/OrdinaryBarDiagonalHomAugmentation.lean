module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction

/-! # Actual ambient and small-vertex Hom augmentations to the original base -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation
open OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution OrdinaryBarDiagonalAmbientHom
open OrdinaryBarFixedAugmentation
variable (C : Type u) [Category.{v} C]

abbrev baseHom (X Y : D C) : SSet.{max u v} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{max u v} (X ⟶ Y))

def smallAugmentation (X Y : D C) : hom C X Y ⟶ baseHom C X Y where
  app n := ↾fun f => ULift.up ((projection C n).map f)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congr($(projection_naturality C θ).map f)
    exact congrArg ULift.up h

def ambientAugmentation (X Y : D C) : ambientHom C X Y ⟶ baseHom C X Y where
  app n := ↾fun f => ULift.up ((projection C n).map f)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congr($(projection_naturality C θ).map f)
    exact congrArg ULift.up h

lemma projection_section (n : SimplexCategoryᵒᵖ) (X : D C) :
    (projection C n).map (sectionAt C n X) = 𝟙 X := by
  change (sourceProjection C n).map
    ((RetractWords.augmentation _ _).map (sectionAt C n X)) = 𝟙 X
  rw [RetractWords.augmentation_section]
  exact (sourceProjection C n).map_id X

lemma projection_projection (n : SimplexCategoryᵒᵖ) (X : D C) :
    (projection C n).map (projectionAt C n X) = 𝟙 X := by
  change (sourceProjection C n).map
    ((RetractWords.augmentation _ _).map (projectionAt C n X)) = 𝟙 X
  rw [RetractWords.augmentation_projection]
  exact (sourceProjection C n).map_id X

lemma transfer_augmentation (X Y : D C) :
    transfer C X Y ≫ smallAugmentation C X Y = ambientAugmentation C X Y := by
  ext n f
  change ULift.up ((projection C n).map (sectionAt C n X ≫ f ≫ projectionAt C n Y)) = _
  rw [Functor.map_comp, Functor.map_comp, projection_section, projection_projection]
  change ULift.up (𝟙 X ≫ (projection C n).map f ≫ 𝟙 Y) =
    ULift.up ((projection C n).map f)
  exact congrArg ULift.up ((Category.id_comp _).trans (Category.comp_id _))

lemma inclusion_augmentation (X Y : D C) :
    inclusion C X Y ≫ ambientAugmentation C X Y = smallAugmentation C X Y := by
  ext n f
  change ULift.up ((projection C n).map (projectionAt C n X ≫ f ≫ sectionAt C n Y)) = _
  rw [Functor.map_comp, Functor.map_comp, projection_section, projection_projection]
  change ULift.up (𝟙 X ≫ (projection C n).map f ≫ 𝟙 Y) =
    ULift.up ((projection C n).map f)
  exact congrArg ULift.up ((Category.id_comp _).trans (Category.comp_id _))

open CategoryTheory.MonoidalCategory

def baseComposition (X Y Z : D C) : baseHom C X Y ⊗ baseHom C Y Z ⟶ baseHom C X Z where
  app _ := ↾fun f => ULift.up (f.1.down ≫ f.2.down)
  naturality _ := by
    intro _ _
    rfl

def baseIdentity (X : D C) : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ baseHom C X X where
  app _ := ↾fun _ => ULift.up (𝟙 X)
  naturality _ := by
    intro _ _
    rfl

lemma augmentation_composition (X Y Z : D C) :
    composition C X Y Z ≫ smallAugmentation C X Z =
      (smallAugmentation C X Y ⊗ₘ smallAugmentation C Y Z) ≫ baseComposition C X Y Z := by
  ext n f
  exact congrArg ULift.up ((projection C n).map_comp f.1 f.2)

lemma augmentation_identity (X : D C) :
    identity C X ≫ smallAugmentation C X X = baseIdentity C X := by
  ext n x
  exact congrArg ULift.up ((projection C n).map_id _)

lemma localized_small_iff_ambient (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (smallAugmentation C X Y)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (ambientAugmentation C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (transfer C X Y)) :=
    OrdinaryBarDiagonalHomRetraction.localized_transfer_isIso C X Y
  rw [← transfer_augmentation, Functor.map_comp]
  exact (isIso_comp_left_iff _ _).symm

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation
