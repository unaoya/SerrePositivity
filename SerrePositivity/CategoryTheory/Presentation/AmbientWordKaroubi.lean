module

public import SerrePositivity.CategoryTheory.Presentation.AmbientWords
public import SerrePositivity.CategoryTheory.Presentation.RetractWordRealization
public import SerrePositivity.CategoryTheory.Presentation.RetractWordIdentities
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-! # Decode formal retract vertices as actual idempotents of the ambient word presentation -/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Idempotents

namespace SerrePositivity.AmbientWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]

abbrev loop (X : C) (t : M) : (sourceFunctor C M).obj X ⟶ (sourceFunctor C M).obj X :=
  (quotient C M).map (word C M X t)

lemma loop_zero_idem (X : C) : loop C M X 0 ≫ loop C M X 0 = loop C M X 0 := by
  rw [← word_mul, zero_mul]

lemma loop_zero_left (X : C) (t : M) : loop C M X 0 ≫ loop C M X t = loop C M X 0 := by
  rw [← word_mul, zero_mul]

lemma loop_zero_right (X : C) (t : M) : loop C M X t ≫ loop C M X 0 = loop C M X 0 := by
  rw [← word_mul, mul_zero]

def toRetractRealization : Realization C M (RetractWords.Obj C M) where
  ambient := RetractWords.sourceFunctor C M
  action X t := (RetractWords.quotient C M).map (RetractWords.word C M X t)
  action_one := RetractWords.quotient_word_one C M
  action_mul X t z := by
    simpa using (CategoryTheory.Quotient.sound (RetractWords.Rel C M)
      (RetractWords.Rel.word_mul X t z)).symm

def toRetract : Obj C M ⥤ RetractWords.Obj C M := (toRetractRealization C M).functor

lemma toRetract_source {X Y : C} (f : X ⟶ Y) :
    (toRetract C M).map ((quotient C M).map (source C M f)) =
      (RetractWords.quotient C M).map (RetractWords.source C M f) :=
  (toRetractRealization C M).functor_source f

lemma toRetract_loop (X : C) (t : M) :
    (toRetract C M).map (loop C M X t) =
      (RetractWords.quotient C M).map (RetractWords.word C M X t) :=
  (toRetractRealization C M).functor_word X t

def smallObject (X : C) : Karoubi (Obj C M) :=
  ⟨(sourceFunctor C M).obj X, loop C M X 0, loop_zero_idem C M X⟩

def decodeRealization : RetractWords.Realization C M (Karoubi (Obj C M)) where
  ambient := sourceFunctor C M ⋙ toKaroubi (Obj C M)
  small := smallObject C M
  section_ X := ⟨loop C M X 0, by
    change loop C M X 0 ≫ loop C M X 0 ≫ 𝟙 _ = loop C M X 0
    rw [Category.comp_id, loop_zero_idem]⟩
  projection X := ⟨loop C M X 0, by
    change 𝟙 _ ≫ loop C M X 0 ≫ loop C M X 0 = loop C M X 0
    rw [Category.id_comp, loop_zero_idem]⟩
  action X t := ⟨loop C M X t, by simp⟩
  action_one X := by
    apply Karoubi.hom_ext
    exact word_one C M X
  action_mul X t z := by
    apply Karoubi.hom_ext
    exact word_mul C M X t z
  split X := by
    apply Karoubi.hom_ext
    exact loop_zero_idem C M X
  action_zero X := by
    apply Karoubi.hom_ext
    exact (loop_zero_idem C M X).symm
  section_action X t := by
    apply Karoubi.hom_ext
    exact loop_zero_left C M X t
  action_projection X t := by
    apply Karoubi.hom_ext
    exact loop_zero_right C M X t

def decode : RetractWords.Obj C M ⥤ Karoubi (Obj C M) := (decodeRealization C M).functor

end SerrePositivity.AmbientWords
