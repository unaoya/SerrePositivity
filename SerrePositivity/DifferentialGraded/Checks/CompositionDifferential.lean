module
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 最終Hom間の合成と消去Leibniz則の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y z : D) :
    ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) (-1) 1 0 (by decide) ≫
      (quotientComposition A D S x y z).f 0 =
    ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (-1) 1 0 (by decide) ≫
      (internalComposition A D S x y z).f 0 :=
  quotientComposition_ι A D S x y z (-1) 1 0 (by decide)

example : quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ⊗
    quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ⟶
    quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit :=
  quotientComposition (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.tensorRightPathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_erasure
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_erasure_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_total_d_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_ι
