module
public import SerrePositivity.DifferentialGraded.Quotient.AppendRightPrepend
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt

/-! # 全path合成と元のHomの先頭作用の結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma internalComposition_prepend (S : Set D) (x y z t : D) :
    (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫ internalComposition A D S x z t =
    (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t ≫ internalPrepend A D S x y t := by
  apply tensorLeftRightCoproduct_hom_ext (homObject A D x y) (internalHom A D S z t)
    (fun w : Word S => term A D w y z)
  intro w
  let s : (homObject A D x y ⊗ term A D w y z) ⊗ internalHom A D S z t ⟶
      (homObject A D x y ⊗ internalHom A D S y z) ⊗ internalHom A D S z t :=
    ((homObject A D x y) ◁ ι A D S y z w) ▷ internalHom A D S z t
  change s ≫ (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    s ≫ (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t ≫ internalPrepend A D S x y t
  have hl : (((homObject A D x y) ◁ ι A D S y z w) ▷ internalHom A D S z t) ≫
      (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    (prependMap A D w x y z ▷ internalHom A D S z t) ≫ appendRight A D w x z t := by
    rw [← comp_whiskerRight_assoc, internalPrepend_ι, comp_whiskerRight,
      Category.assoc, internalComposition_left_ι]
  have hm : (((homObject A D x y) ◁ ι A D S y z w) ▷ internalHom A D S z t) ≫
      (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t =
    (α_ (homObject A D x y) (term A D w y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ appendRight A D w y z t := by
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_ι]
  have hr := congrArg (fun f => f ≫ internalPrepend A D S x y t) hm
  simpa only [Category.assoc] using hl.trans ((appendRight_prepend A D w x y z t).trans hr.symm)

end SerrePositivity.DifferentialGraded.DGQuotient
