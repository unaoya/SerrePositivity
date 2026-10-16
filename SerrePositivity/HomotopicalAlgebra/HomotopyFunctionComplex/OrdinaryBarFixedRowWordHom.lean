module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.FreeWordHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed

/-! # The actual fixed-outer-degree word Hom augmentation is inverted -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C] (N : ℕ) (X Y : D C)

abbrev hom : SSet.{max u v} := FreeWordHom.hom (degree (D C) N) X Y

lemma hom_obj (n : SimplexCategoryᵒᵖ) : (hom C N X Y).obj n =
    ((AmbientWords.sourceFunctor (degree (D C) (N + 1)) (WordSegment.degree.{max u v} n)).obj X ⟶
      (AmbientWords.sourceFunctor (degree (D C) (N + 1)) (WordSegment.degree.{max u v} n)).obj Y) :=
  rfl

def augmentation : hom C N X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
    (ULift.{max u v} (FreeGeneratorDegeneracies.hom (N + 1) X Y)) :=
  FreeWordHom.augmentation (degree (D C) N) X Y

lemma augmentation_app (n : SimplexCategoryᵒᵖ) (f : (hom C N X Y).obj n) :
    (augmentation C N X Y).app n f = ULift.up
      ((AmbientWords.augmentation (degree (D C) (N + 1)) (WordSegment.degree.{max u v} n)).map f) :=
  FreeWordHom.augmentation_app (degree (D C) N) X Y n f

lemma map_eq {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (f : (hom C N X Y).obj n) :
    (hom C N X Y).map θ f =
      (AmbientWords.map (𝟭 (degree (D C) (N + 1))) (WordSegment.degreeMap θ)).map f :=
  FreeWordHom.map_eq (degree (D C) N) X Y θ f

lemma localized_augmentation_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (augmentation C N X Y)) :=
  FreeWordHom.localized_augmentation_isIso (degree (D C) N) X Y

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom
