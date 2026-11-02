module
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Data.ZMod.Basic

/-! # 最終Hom微分・元のHomの包含・空部分圏比較の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y : D) (i : ℤ) :
    (quotientHom A D S x y).d i (i + 1) =
      (internalHom A D S x y).d i (i + 1) + (erasure A D S x y).v i (i + 1) rfl :=
  quotientHom_d A D S x y i
example (S : Set D) (x y : D) : homObject A D x y ⟶ quotientHom A D S x y :=
  originalHomInclusion A D S x y
example (x y : D) : homObject A D x y ≅ quotientHom A D ∅ x y := quotientHom_emptyIso A D x y
example (i : ℤ) :
    (quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit).d i (i + 1) ≫
      (quotientHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit).d (i + 1) (i + 2) = 0 :=
  HomologicalComplex.d_comp_d _ _ _ _

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientHom
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientHom_X
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientHom_d
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.originalHomInclusion
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.originalHomInclusion_f
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasure_empty
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientHom_emptyIso
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientHom_emptyIso_hom
