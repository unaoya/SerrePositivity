module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionPrefix
public import Mathlib.Data.ZMod.Basic

/-! # 全path合成と先頭Hom・ε追加の可換図式の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {S : Set D} (b : S) (x y z : D) :
    (prefixPath A D b x y ▷ internalHom A D S y z) ≫ internalComposition A D S x y z =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      (internalHom A D S y z)).hom ≫ (homObject A D x b.val) ◁
        ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
          (epsilonComplex A) ◁ internalComposition A D S b.val y z) ≫ prefixPath A D b x z :=
  internalComposition_prefixPath A D b x y z
example (b : (Set.univ : Set PUnit.{1})) :
    (prefixPath (ZMod 2) PUnit.{1} b PUnit.unit PUnit.unit ▷
      internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit) ≫
      internalComposition (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit =
    (α_ (homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit)
      (epsilonComplex (ZMod 2) ⊗ internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)
      (internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)).hom ≫
      (homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit) ◁
        ((α_ (epsilonComplex (ZMod 2))
          (internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)
          (internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)).hom ≫
          (epsilonComplex (ZMod 2)) ◁ internalComposition (ZMod 2) PUnit.{1} Set.univ
            PUnit.unit PUnit.unit PUnit.unit) ≫ prefixPath (ZMod 2) PUnit.{1} b PUnit.unit PUnit.unit :=
  internalComposition_prefixPath (ZMod 2) PUnit.{1} b PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.composition_prefix_left_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.composition_prefix_middle_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.composition_prefix_outer_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.composition_prefix_restrict
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_prefixPath
