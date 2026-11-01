module
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 元のHom包含との比較と最終Homの左単位の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y z : D) :
    (originalHomInclusion A D S x y ⊗ₘ originalHomInclusion A D S y z) ≫
      quotientComposition A D S x y z =
    eComp (Complex A) x y z ≫ originalHomInclusion A D S x z :=
  quotientComposition_original A D S x y z

example : (λ_ (quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)).inv ≫
    quotientIdentity (ZMod 2) PUnit.{1} Set.univ PUnit.unit ▷
      quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ≫
    quotientComposition (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit = 𝟙 _ :=
  quotientComposition_left_unit (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_f
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_original
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientIdentity
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientIdentity_f
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_left_unit
