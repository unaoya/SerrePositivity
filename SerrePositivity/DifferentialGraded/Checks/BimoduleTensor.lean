module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import Mathlib.Data.ZMod.Basic

/-! # 多対象dg bimoduleの相対tensor合成と残る作用の検査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
example (P : Bimodule A B C) (Q : Bimodule A C E) : Bimodule A B E :=
  BimoduleTensor.compose A B C E P Q
example (P Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    Bimodule (ZMod 2) PUnit.{1} PUnit.{1} :=
  BimoduleTensor.compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q

#print axioms BimoduleTensor.rightAt
#print axioms BimoduleTensor.leftAt
#print axioms BimoduleTensor.interchange
#print axioms BimoduleTensor.paramTrans
#print axioms BimoduleTensor.paramTrans_unit
#print axioms BimoduleTensor.paramTrans_comp
#print axioms BimoduleTensor.compose
#print axioms BimoduleTensor.compose_value
#print axioms BimoduleTensor.compose_rightMap
#print axioms BimoduleTensor.compose_leftMap_π
