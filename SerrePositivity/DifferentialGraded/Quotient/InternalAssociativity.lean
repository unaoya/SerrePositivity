module
public import SerrePositivity.DifferentialGraded.Quotient.AppendRightAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt

/-! # 内部全path合成の結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma internalComposition_assoc (S : Set D) (x y z t : D) :
    (internalComposition A D S x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    (α_ (internalHom A D S x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      internalHom A D S x y ◁ internalComposition A D S y z t ≫
        internalComposition A D S x y t := by
  apply tensorRightTwoCoproduct_hom_ext (fun w : Word S => term A D w x y)
    (internalHom A D S y z) (internalHom A D S z t) (internalHom A D S x t)
  intro w
  change ((ι A D S x y w ▷ internalHom A D S y z) ▷ internalHom A D S z t) ≫
      (internalComposition A D S x y z ▷ internalHom A D S z t) ≫
        internalComposition A D S x z t = _
  rw [← comp_whiskerRight_assoc, internalComposition_left_ι,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (appendRight A D w x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    (α_ (term A D w x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (term A D w x y) ◁ internalComposition A D S y z t ≫
        (ι A D S x y w ▷ internalHom A D S y t) ≫ internalComposition A D S x y t
  rw [internalComposition_left_ι, appendRight_assoc]

end SerrePositivity.DifferentialGraded.DGQuotient
