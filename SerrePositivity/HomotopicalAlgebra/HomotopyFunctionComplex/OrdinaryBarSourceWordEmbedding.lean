module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection

/-! # The actual source Hom maps into ambient and small-vertex word Hom

All simplicial operators and the original augmentations commute. The
small-vertex map sandwiches by the retract maps and is not claimed to
preserve composition.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution
open OrdinaryBarDiagonalAmbientHom OrdinaryBarDiagonalHomAugmentation
variable (C : Type u) [Category.{v} C] (X Y : D C)

def ambient : UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) ⟶
    ambientHom C X Y where
  app n := ↾fun f => (RetractWords.sourceFunctor (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n)).map f.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    change (RetractWords.sourceFunctor (degree (D C) (m.unop.len + 1))
        (WordSegment.degree.{max u v} m)).map
          ((OrdinaryBarFixedSource.literalMap C θ).map f.down) =
      (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1))) (WordSegment.degreeMap θ)).map
        ((RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
          (MonoidWithZeroHom.id _)).map
            ((RetractWords.sourceFunctor (degree (D C) (n.unop.len + 1))
              (WordSegment.degree.{max u v} n)).map f.down))
    have h₁ := RetractWords.map_source
      (C := degree (D C) (n.unop.len + 1))
      (OrdinaryBarFixedSource.literalMap C θ)
      (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) f.down
    have h₂ := RetractWords.map_source
      (C := degree (D C) (m.unop.len + 1)) (𝟭 _) (WordSegment.degreeMap θ)
      ((OrdinaryBarFixedSource.literalMap C θ).map f.down)
    exact ((congrArg ((RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1)))
      (WordSegment.degreeMap θ)).map) h₁).trans h₂).symm


lemma ambient_augmentation : ambient C X Y ≫ ambientAugmentation C X Y =
    OrdinaryBarSourceHom.augmentation C X Y := by
  ext n f
  change ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map
      ((RetractWords.augmentation _ _).map
        ((RetractWords.quotient _ _).map (RetractWords.source _ _ f.down)))) = _
  rw [RetractWords.augmentation_source]
  rfl

def small : UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) ⟶ hom C X Y :=
  ambient C X Y ≫ transfer C X Y

lemma small_augmentation : small C X Y ≫ smallAugmentation C X Y =
    OrdinaryBarSourceHom.augmentation C X Y := by
  rw [small, Category.assoc, transfer_augmentation, ambient_augmentation]

lemma ambient_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (ambient C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (ambientAugmentation C X Y)) :=
    (localized_small_iff_ambient C X Y).mp
      (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y)
  have h := congrArg AnodyneHomotopy.anodyneQ.map (ambient_augmentation C X Y)
  rw [Functor.map_comp] at h
  have : IsIso (AnodyneHomotopy.anodyneQ.map (ambient C X Y) ≫
      AnodyneHomotopy.anodyneQ.map (ambientAugmentation C X Y)) :=
    h.symm ▸ OrdinaryBarSourceContraction.source_augmentation_isIso C X Y
  exact (isIso_comp_right_iff _ _).mp this

lemma small_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (small C X Y)) := by
  have := ambient_isIso C X Y
  have := OrdinaryBarDiagonalHomRetraction.localized_transfer_isIso C X Y
  rw [small, Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding
