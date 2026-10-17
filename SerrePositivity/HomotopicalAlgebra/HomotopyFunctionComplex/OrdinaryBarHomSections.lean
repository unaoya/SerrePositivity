module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding

/-! # Split epimorphisms on the Hom augmentations, in every simplicial degree

The sections commute with all simplex operators. They are Hom sections,
not category sections, and supply no strict action on the original base.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections
open OrdinaryBarFreeResolutionSeed OrdinaryBarDiagonalHomAugmentation
variable (C : Type u) [Category.{v} C] (X Y : D C)

def source : SplitEpi (OrdinaryBarSourceHom.augmentation C X Y) where
  section_ := OrdinaryBarSourceSection.section_ C X Y
  id := OrdinaryBarSourceSection.section_comp_augmentation C X Y

def ambient : SplitEpi (ambientAugmentation C X Y) where
  section_ := (source C X Y).section_ ≫ OrdinaryBarSourceWordEmbedding.ambient C X Y
  id := by
    rw [Category.assoc, OrdinaryBarSourceWordEmbedding.ambient_augmentation]
    exact (source C X Y).id

def small : SplitEpi (smallAugmentation C X Y) where
  section_ := (source C X Y).section_ ≫ OrdinaryBarSourceWordEmbedding.small C X Y
  id := by
    rw [Category.assoc, OrdinaryBarSourceWordEmbedding.small_augmentation]
    exact (source C X Y).id

lemma ambient_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((ambientAugmentation C X Y).app n) := by
  intro f
  exact ⟨(ambient C X Y).section_.app n f,
    types_congr_hom (congr_app (ambient C X Y).id n) f⟩

lemma small_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((smallAugmentation C X Y).app n) := by
  intro f
  exact ⟨(small C X Y).section_.app n f,
    types_congr_hom (congr_app (small C X Y).id n) f⟩

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections
