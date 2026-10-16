module

public import SerrePositivity.CategoryTheory.Presentation.AmbientWords

/-! # The actual augmentation forgets all ambient word actions -/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AmbientWords
variable (C : Type u) [Category.{v} C] (M : Type w) [Monoid M]

def augmentationRealization : Realization C M C where
  ambient := 𝟭 C
  action X _ := 𝟙 X
  action_one _ := rfl
  action_mul _ _ _ := (Category.id_comp _).symm

def augmentation : Obj C M ⥤ C := (augmentationRealization C M).functor

lemma augmentation_source {X Y : C} (f : X ⟶ Y) :
    (augmentation C M).map ((sourceFunctor C M).map f) = f :=
  (augmentationRealization C M).functor_source f

lemma augmentation_word (X : C) (t : M) :
    (augmentation C M).map ((quotient C M).map (word C M X t)) = 𝟙 X :=
  (augmentationRealization C M).functor_word X t

end SerrePositivity.AmbientWords
