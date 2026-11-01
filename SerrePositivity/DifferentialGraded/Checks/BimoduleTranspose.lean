module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import Mathlib.Data.ZMod.Basic

/-! # bimodule転置と全Hom持ち上げの検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]
example (M : Bimodule A B C) : DGFunctor A Bᵒᵖ (LeftModule A C) := M.transposeDG
example (M : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    DGFunctor (ZMod 2) PUnit.{1}ᵒᵖ (LeftModule (ZMod 2) PUnit.{1}) := M.transposeDG

#print axioms Bimodule.transposeInterchange
#print axioms Bimodule.transposeParam
#print axioms Bimodule.transposeHom
#print axioms Bimodule.transposeHom_π
#print axioms Bimodule.transposeDG
