module
public import SerrePositivity.DifferentialGraded.Quotient.RightIdentity
public import Mathlib.Data.ZMod.Basic

/-! # 全pathと最終Homの右単位の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {S : Set D} (w : Word S) (x y : D) :
    (ρ_ (term A D w x y)).inv ≫ term A D w x y ◁ internalIdentity A D S y ≫
      appendRight A D w x y y = ι A D S x y w := appendRight_right_unit A D w x y

example : (ρ_ (quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)).inv ≫
    quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ◁
      quotientIdentity (ZMod 2) PUnit.{1} Set.univ PUnit.unit ≫
    quotientComposition (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit = 𝟙 _ :=
  quotientComposition_right_unit (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.tensorCarry_right_unit
#print axioms SerrePositivity.DifferentialGraded.complexRightUnitor_inv_apply
#print axioms SerrePositivity.DifferentialGraded.rightUnitor_hom_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_right_unit
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_right_unit
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_right_unit
