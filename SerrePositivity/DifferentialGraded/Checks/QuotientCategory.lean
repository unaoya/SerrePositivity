module
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Data.ZMod.Basic

/-! # path商の主豊穣dg構造・結合則・通常順符号の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : DGCategory A (QuotientObject D S) := inferInstance
example (S : Set D) : DGFunctor A D (QuotientObject D S) := inclusion A D S
example : DGCategory (ZMod 2) (QuotientObject PUnit.{1} Set.univ) := inferInstance

example (S : Set D) (x y z : D)
    (f : (quotientHom A D S x y).X (-1)) (g : (quotientHom A D S y z).X 1) :
    (quotientComposition A D S x y z).f 0
      (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) (-1) 1 0 (by decide)
        (f ⊗ₜ[A] g)) =
    (((-1 : ℤ) * 1).negOnePow) • compose A (x := (⟨x⟩ : QuotientObject D S))
      (y := (⟨y⟩ : QuotientObject D S)) (z := (⟨z⟩ : QuotientObject D S)) g f (by decide) :=
  quotientComposition_eq_signed_compose A D S x y z (-1) 1 0 (by decide) f g

#print axioms SerrePositivity.DifferentialGraded.tensorCarry_assoc
#print axioms SerrePositivity.DifferentialGraded.tensorRightTwoCoproduct_hom_ext
#print axioms SerrePositivity.DifferentialGraded.tensorComposition_assoc_apply
#print axioms SerrePositivity.DifferentialGraded.tensorComposition_assoc_of_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_assoc
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_assoc
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_assoc
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientObjectEquiv
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientDGCategory
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.inclusion
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientComposition_eq_signed_compose
