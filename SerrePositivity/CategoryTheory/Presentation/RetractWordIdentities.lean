module

public import SerrePositivity.CategoryTheory.Presentation.RetractWords

/-! # The defining retract relations as equalities of actual quotient arrows -/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]

lemma quotient_word_one (X : C) : (quotient C M).map (word C M X 1) = 𝟙 _ := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.word_one X)

lemma quotient_word_zero (X : C) :
    (quotient C M).map (word C M X 0) =
      (quotient C M).map (projection C M X) ≫ (quotient C M).map (section_ C M X) := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.word_zero X)

lemma quotient_split (X : C) :
    (quotient C M).map (section_ C M X) ≫ (quotient C M).map (projection C M X) = 𝟙 _ := by
  simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.split X)

end SerrePositivity.RetractWords
