module
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import Mathlib.Data.ZMod.Basic

/-! # 二重balanced族の右反復tensorへの降下の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
open SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (T : Complex A)
    (a : DoubleFamily A C E Q R N T) : rightObj A C E Q R N ⟶ T := rightDesc A C E a

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (T : Complex A)
    (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    rightι A C E Q R N c e ≫ rightDesc A C E a = (a.row e).val c :=
  rightι_rightDesc A C E a c e

example (Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (R : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (T : Complex (ZMod 2))
    (a : DoubleFamily (ZMod 2) PUnit.{1} PUnit.{1} Q R N T) :
    rightObj (ZMod 2) PUnit.{1} PUnit.{1} Q R N ⟶ T :=
  rightDesc (ZMod 2) PUnit.{1} PUnit.{1} a

#print axioms DoubleFamily.balanceC_of_sums
#print axioms columnDesc_balanced_element
#print axioms rightFamily
#print axioms rightDesc
#print axioms rightι_rightDesc
