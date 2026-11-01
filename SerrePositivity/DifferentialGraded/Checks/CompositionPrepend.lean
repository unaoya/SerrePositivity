module
public import SerrePositivity.DifferentialGraded.Quotient.Append
public import Mathlib.Data.ZMod.Basic

/-! # 先頭Hom作用と連結の有限・全path結合図式の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y z t : D) :
    (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫ internalComposition A D S x z t =
    (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t ≫ internalPrepend A D S x y t :=
  internalComposition_prepend A D S x y z t
example (S : Set PUnit.{1}) :
    (internalPrepend (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit PUnit.unit ▷
      internalHom (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit) ≫
      internalComposition (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit PUnit.unit =
    (α_ (homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit)
      (internalHom (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit)
      (internalHom (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit)).hom ≫
      (homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit) ◁
        internalComposition (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit PUnit.unit ≫
        internalPrepend (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit PUnit.unit :=
  internalComposition_prepend (ZMod 2) PUnit.{1} S PUnit.unit PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.tensorJoin_right_action
#print axioms SerrePositivity.DifferentialGraded.tensorLeftRightCoproduct_hom_ext
#print axioms SerrePositivity.DifferentialGraded.tensorLeftTwoRightCoproduct_hom_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendMap_prepend
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_prepend
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_prepend
