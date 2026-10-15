module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # The actual diagonal and its ordinary right adjoint

The diagonal is restriction along Delta-op to its square after uncurrying.
Right Kan extension and currying construct its actual right adjoint. No
Quillen compatibility or weak-equivalence preservation is assumed here.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory

namespace SerrePositivity.BisimplicialModel

abbrev currying : (SimplexCategoryᵒᵖ ⥤ SSet.{v}) ≌
    ((SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type v) := Functor.currying

abbrev diagonal : (SimplexCategoryᵒᵖ ⥤ SSet.{v}) ⥤ SSet.{v} :=
  currying.functor ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ
    (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type v)).obj (Functor.diag SimplexCategoryᵒᵖ)

abbrev rightAdjoint : SSet.{v} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{v} :=
  (Functor.diag SimplexCategoryᵒᵖ).ran ⋙ currying.inverse

/-- The genuine adjunction for the actual diagonal restriction. -/
def diagonalAdjunction : diagonal.{v} ⊣ rightAdjoint.{v} :=
  currying.toAdjunction.comp ((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v))

instance diagonal_isLeftAdjoint : diagonal.{v}.IsLeftAdjoint :=
  diagonalAdjunction.isLeftAdjoint

instance rightAdjoint_isRightAdjoint : rightAdjoint.{v}.IsRightAdjoint :=
  diagonalAdjunction.isRightAdjoint

@[simp]
lemma diagonal_obj (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    diagonal.obj B = HomotopyFunctionComplex.DiagonalFrame.obj B := rfl

@[simp]
lemma diagonal_map {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (a : B ⟶ B') :
    diagonal.map a = HomotopyFunctionComplex.DiagonalFrame.map a := rfl

end SerrePositivity.BisimplicialModel
