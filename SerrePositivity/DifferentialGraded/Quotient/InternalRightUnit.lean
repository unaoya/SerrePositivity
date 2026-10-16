module
public import SerrePositivity.DifferentialGraded.Quotient.AppendRightUnit

/-! # 内部path合成の全直和における右単位 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma internalComposition_right_unit (S : Set D) (x y : D) :
    (ρ_ (internalHom A D S x y)).inv ≫ internalHom A D S x y ◁ internalIdentity A D S y ≫
      internalComposition A D S x y y = 𝟙 _ := by
  apply hom_ext A D S x y
  intro w
  simp only [Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    internalComposition_left_ι, appendRight_right_unit]

end SerrePositivity.DifferentialGraded.DGQuotient
