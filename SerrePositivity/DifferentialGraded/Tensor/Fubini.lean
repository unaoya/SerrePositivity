module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniRightRestriction

/-! # dg加群の相対tensorのFubini同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

@[simp]
lemma leftRestrict_row_val {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : leftObj A C E Q R N ⟶ T) (c : C) (e : E) :
    ((leftRestrict A C E f).row e).val c = leftι A C E Q R N c e ≫ f := rfl

@[simp]
lemma rightRestrict_row_val {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : rightObj A C E Q R N ⟶ T) (c : C) (e : E) :
    ((rightRestrict A C E f).row e).val c = rightι A C E Q R N c e ≫ f := rfl

/-- R⊗_E(Q⊗_C N)≅(R⊗_E Q)⊗_C N。生成元の順をR,Q,Nに保つ。 -/
def iso (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) :
    leftObj A C E Q R N ≅ rightObj A C E Q R N where
  hom := leftDesc A C E (rightRestrict A C E (𝟙 (rightObj A C E Q R N)))
  inv := rightDesc A C E (leftRestrict A C E (𝟙 (leftObj A C E Q R N)))
  hom_inv_id := by
    apply left_hom_ext A C E Q R N
    intro c e
    simp only [leftι_leftDesc_assoc, rightRestrict_row_val, Category.comp_id,
      rightι_rightDesc, leftRestrict_row_val]
  inv_hom_id := by
    apply right_hom_ext A C E Q R N
    intro c e
    simp only [rightι_rightDesc_assoc, leftRestrict_row_val, Category.comp_id,
      leftι_leftDesc, rightRestrict_row_val]

@[reassoc (attr := simp)]
lemma leftι_iso_hom (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (c : C) (e : E) :
    leftι A C E Q R N c e ≫ (iso A C E Q R N).hom = rightι A C E Q R N c e := by
  simp only [iso, leftι_leftDesc, rightRestrict_row_val, Category.comp_id]

@[reassoc (attr := simp)]
lemma rightι_iso_inv (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (c : C) (e : E) :
    rightι A C E Q R N c e ≫ (iso A C E Q R N).inv = leftι A C E Q R N c e := by
  simp only [iso, rightι_rightDesc, leftRestrict_row_val, Category.comp_id]

/-- Fubini同型を通した降下は同じ二重balanced族の右降下に一致する。 -/
lemma iso_inv_leftDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    (iso A C E Q R N).inv ≫ leftDesc A C E a = rightDesc A C E a := by
  apply right_hom_ext A C E Q R N
  intro c e
  simp only [rightι_iso_inv_assoc, leftι_leftDesc, rightι_rightDesc]

lemma iso_hom_rightDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    (iso A C E Q R N).hom ≫ rightDesc A C E a = leftDesc A C E a := by
  apply left_hom_ext A C E Q R N
  intro c e
  simp only [leftι_iso_hom_assoc, rightι_rightDesc, leftι_leftDesc]

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
