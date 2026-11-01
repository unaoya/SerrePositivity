module
public import SerrePositivity.DifferentialGraded.Quotient.Scalar
public import Mathlib.Data.ZMod.Basic

/-! # 全path直和の内部合成と左単位の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y z : D) :
    (originalHom A D S x y ⊗ₘ originalHom A D S y z) ≫ internalComposition A D S x y z =
      eComp (Complex A) x y z ≫ originalHom A D S x z :=
  internalComposition_original_original A D S x y z
example (S : Set D) (x y : D) :
    (λ_ (internalHom A D S x y)).inv ≫ internalIdentity A D S x ▷ internalHom A D S x y ≫
      internalComposition A D S x x y = 𝟙 _ := internalComposition_left_unit A D S x y
example (b : (Set.univ : Set PUnit.{1}))
    (f : (term (ZMod 2) PUnit.{1} [b] PUnit.unit PUnit.unit).X (-1))
    (g : (term (ZMod 2) PUnit.{1} [] PUnit.unit PUnit.unit).X 1) :
    (internalComposition (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit).f 0
      (ιTensorObj (internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit)
        (internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit) (-1) 1 0 (by omega)
        ((ι (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit [b]).f (-1) f ⊗ₜ[ZMod 2]
          (ι (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit []).f 1 g)) =
    (ι (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ([b] ++ [])).f 0
      ((appendMap (ZMod 2) PUnit.{1} [b] [] PUnit.unit PUnit.unit PUnit.unit).f 0
        (ιTensorObj (term (ZMod 2) PUnit.{1} [b] PUnit.unit PUnit.unit)
          (term (ZMod 2) PUnit.{1} [] PUnit.unit PUnit.unit) (-1) 1 0 (by omega)
          (f ⊗ₜ[ZMod 2] g))) :=
  internalComposition_apply (ZMod 2) PUnit.{1} Set.univ _ _ _ [b] [] (-1) 1 0 (by omega) f g

#print axioms SerrePositivity.DifferentialGraded.tensorLeftCoproductIsColimit
#print axioms SerrePositivity.DifferentialGraded.tensorRightCoproductIsColimit
#print axioms SerrePositivity.DifferentialGraded.tensorCoproductRightDesc
#print axioms SerrePositivity.DifferentialGraded.tensorCoproductRightDesc_ι
#print axioms SerrePositivity.DifferentialGraded.tensorCoproductDesc
#print axioms SerrePositivity.DifferentialGraded.tensorCoproductDesc_left
#print axioms SerrePositivity.DifferentialGraded.tensorCoproductDesc_ι
#print axioms SerrePositivity.DifferentialGraded.tensorCoproduct_hom_ext
#print axioms SerrePositivity.DifferentialGraded.tensorJoin_left_unit
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_left_unit
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_hom_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_original_left
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_original_original
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalIdentity
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_left_unit
