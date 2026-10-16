module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 二つの右tensor因子を持つ余積からの射の判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorRightTwoCoproduct_hom_ext {J : Type v}
    (F : J → Complex A) [HasCoproduct F] (Q R T : Complex A)
    (f g : ((∐ F) ⊗ Q) ⊗ R ⟶ T)
    (h : ∀ j, ((Sigma.ι F j ▷ Q) ▷ R) ≫ f = ((Sigma.ι F j ▷ Q) ▷ R) ≫ g) : f = g := by
  let := (tensorRightHomAdjunction Q).isLeftAdjoint
  let := (tensorRightHomAdjunction R).isLeftAdjoint
  apply (isColimitOfHasCoproductOfPreservesColimit (tensorRight Q ⋙ tensorRight R) F).hom_ext
  rintro ⟨j⟩
  exact h j

end SerrePositivity.DifferentialGraded
