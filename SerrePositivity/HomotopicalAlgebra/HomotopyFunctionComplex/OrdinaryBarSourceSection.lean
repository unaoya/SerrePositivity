module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction

/-! # A simplicial section on each Hom of the actual source augmentation

This section is on individual Hom simplicial sets. It is not a functorial
section of the category augmentation and asserts no composition law.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection
open OrdinaryBarFreeResolutionSeed OrdinaryBarSourceContraction OppositeHomotopy
variable (C : Type u) [Category.{v} C] (X Y : D C)

def section_ : OrdinaryBarDiagonalHomAugmentation.baseHom C X Y ⟶
    UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  (baseReverseIso C X Y).inv ≫
    reverseMap (OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y).section_ ≫
      (doubleIso (UniverseLift.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y))).hom

lemma section_comp_augmentation : section_ C X Y ≫ OrdinaryBarSourceHom.augmentation C X Y =
    𝟙 (OrdinaryBarDiagonalHomAugmentation.baseHom C X Y) := by
  ext n f
  exact types_congr_hom (congr_app
    (OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y).section_comp_hom n) f

lemma augmentation_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((OrdinaryBarSourceHom.augmentation C X Y).app n) := by
  intro f
  exact ⟨(section_ C X Y).app n f,
    types_congr_hom (congr_app (section_comp_augmentation C X Y) n) f⟩

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection
