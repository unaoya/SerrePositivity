module
public import SerrePositivity.DifferentialGraded.Quotient.Append
public import Mathlib.Data.ZMod.Basic

/-! # 左有限pathを固定した連結と非空語再帰の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (w v : Word S) (x y z : D) :
    (term A D w x y ◁ ι A D S y z v) ≫ appendRight A D w x y z =
      appendMap A D w v x y z ≫ ι A D S x z (w ++ v) := appendRight_ι A D w v x y z
example (S : Set D) (x y z : D) :
    appendRight A D ([] : Word S) x y z = internalPrepend A D S x y z := appendRight_nil A D S x y z
example (b : (Set.univ : Set PUnit.{1})) :
    term (ZMod 2) PUnit.{1} [b] PUnit.unit PUnit.unit ⊗
      internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ⟶
        internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit :=
  appendRight (ZMod 2) PUnit.{1} [b] PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalComposition_left_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_nil
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_cons
