module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 複数のtensor因子を持つ余積からの射の判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A] {I : Type v}

lemma tensorLeftRightCoproduct_hom_ext (K R : Complex A) (F : I → Complex A) [HasCoproduct F]
    {T : Complex A} (f g : (K ⊗ ∐ F) ⊗ R ⟶ T)
    (h : ∀ i, ((K ◁ Sigma.ι F i) ▷ R) ≫ f = ((K ◁ Sigma.ι F i) ▷ R) ≫ g) : f = g := by
  let := (tensorRightHomAdjunction R).isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit (tensorLeft K ⋙ tensorRight R) F).hom_ext
  rintro ⟨i⟩
  exact h i

lemma tensorLeftTwoRightCoproduct_hom_ext (L K R : Complex A) (F : I → Complex A)
    [HasCoproduct F] {T : Complex A} (f g : (L ⊗ (K ⊗ ∐ F)) ⊗ R ⟶ T)
    (h : ∀ i, ((L ◁ (K ◁ Sigma.ι F i)) ▷ R) ≫ f =
      ((L ◁ (K ◁ Sigma.ι F i)) ▷ R) ≫ g) : f = g := by
  let := (tensorRightHomAdjunction R).isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft K ⋙ tensorLeft L ⋙ tensorRight R) F).hom_ext
  rintro ⟨i⟩
  exact h i

end SerrePositivity.DifferentialGraded
