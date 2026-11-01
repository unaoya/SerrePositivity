module
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 最終Hom微分に関する先頭Hom作用の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y z : D) :
    homObject A D x y ⊗ quotientHom A D S y z ⟶ quotientHom A D S x z :=
  quotientPrepend A D S x y z
example (S : Set D) (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (homObject A D x y) (quotientHom A D S y z) i j n hn ≫
      (quotientPrepend A D S x y z).f n =
    ιTensorObj (homObject A D x y) (internalHom A D S y z) i j n hn ≫
      (internalPrepend A D S x y z).f n := quotientPrepend_ι A D S x y z i j n hn
example : homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit ⊗
    quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ⟶
      quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit :=
  quotientPrepend (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalPrepend_total_d_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientPrepend
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientPrepend_ι
