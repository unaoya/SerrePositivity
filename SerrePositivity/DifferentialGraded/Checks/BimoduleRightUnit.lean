module
public import SerrePositivity.DifferentialGraded.Tensor.RightUnit
public import Mathlib.Data.ZMod.Basic

/-! # 対角bimoduleと右単位同型の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]
example : Bimodule A B B := Bimodule.diagonal A B
example (P : Bimodule A B C) (c : C) :
    ForgetEnrichment.of (Complex A)
      ((BimoduleTensor.compose A B C C P (Bimodule.diagonal A C)).rightAt c) ≅
        ForgetEnrichment.of (Complex A) (P.rightAt c) := BimoduleTensor.rightUnitIso A B C P c
example (P : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    ForgetEnrichment.of (Complex (ZMod 2))
      ((BimoduleTensor.compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P
        (Bimodule.diagonal (ZMod 2) PUnit.{1})).rightAt PUnit.unit) ≅
    ForgetEnrichment.of (Complex (ZMod 2)) (P.rightAt PUnit.unit) :=
  BimoduleTensor.rightUnitIso (ZMod 2) PUnit.{1} PUnit.{1} P PUnit.unit

#print axioms Bimodule.diagonal
#print axioms Bimodule.diagonal_rightAt
#print axioms Bimodule.diagonal_value
#print axioms Bimodule.diagonal_leftAt
#print axioms BimoduleTensor.rightUnitValueIso
#print axioms BimoduleTensor.rightUnitValue_naturality
#print axioms BimoduleTensor.rightUnitIso
#print axioms BimoduleTensor.rightUnitIso_hom_eval
#print axioms BimoduleTensor.rightUnitIso_inv_eval
#print axioms BimoduleTensor.rightUnitValue_left_naturality
#print axioms BimoduleTensor.rightUnitIso_naturality
#print axioms moduleMorphismComponent
#print axioms moduleHomPostcompose
#print axioms moduleHomPrecompose
#print axioms moduleHomPostcompose_π
#print axioms moduleHomPrecompose_π
#print axioms BimoduleTensor.rightUnitIso_hom_component
