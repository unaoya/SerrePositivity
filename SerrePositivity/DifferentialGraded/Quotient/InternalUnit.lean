module
public import SerrePositivity.DifferentialGraded.Quotient.InternalComposition
public import SerrePositivity.DifferentialGraded.Quotient.PrependUnit

/-! # 全path直和の合成の左単位

内部微分の圏で単位写像と左単位則を構成する。最終Hom微分への移送は後続で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元のdg圏の単位を空pathへ入れた写像。 -/
def internalIdentity (S : Set D) (x : D) : 𝟙_ (Complex A) ⟶ internalHom A D S x x :=
  eId (Complex A) x ≫ originalHom A D S x x

lemma internalComposition_left_unit (S : Set D) (x y : D) :
    (λ_ (internalHom A D S x y)).inv ≫ internalIdentity A D S x ▷ internalHom A D S x y ≫
      internalComposition A D S x x y = 𝟙 _ := by
  apply hom_ext A D S x y
  intro w
  simp only [internalIdentity, comp_whiskerRight, Category.assoc, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    ← tensorHom_def_assoc, internalComposition_original_left, prependMap_left_unit_assoc]

end SerrePositivity.DifferentialGraded.DGQuotient
