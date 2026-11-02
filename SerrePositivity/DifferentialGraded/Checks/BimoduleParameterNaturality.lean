module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import Mathlib.Data.ZMod.Basic

/-! # 全Hom自然な相対tensorのパラメータ付き変換の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C]
variable {K : Complex A} {P P' : Bimodule A B C} {Q Q' : Bimodule A C E}

-- Eのsmall性、Kの閉性・有界性は不要。
example (τ : BimoduleParamTrans A B C K P P') :
    BimoduleParamTrans A B E K (compose A B C E P Q) (compose A B C E P' Q) :=
  firstParam A B C E Q τ

example (τ : BimoduleParamTrans A C E K Q Q') :
    BimoduleParamTrans A B E K (compose A B C E P Q) (compose A B C E P Q') :=
  secondParam A B C E P τ

example (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    Bimodule.paramValue A B E (firstParam A B C E Q τ) b e =
      firstParamHom A B C E Q τ b e := firstParam_value A B C E Q τ b e

example (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    Bimodule.paramValue A B E (secondParam A B C E P τ) b e =
      secondParamHom A B C E P τ b e := secondParam_value A B C E P τ b e

variable [Small.{u} E] {R R' : Bimodule A E F}
-- 三変数の各々について、左右の括弧付けに実際の変換を構成できる。
example (τ : BimoduleParamTrans A B C K P P') :
    BimoduleParamTrans A B F K (compose A B E F (compose A B C E P Q) R)
      (compose A B E F (compose A B C E P' Q) R) :=
  firstParam A B E F R (firstParam A B C E Q τ)

example (τ : BimoduleParamTrans A B C K P P') :
    BimoduleParamTrans A B F K (compose A B C F P (compose A C E F Q R))
      (compose A B C F P' (compose A C E F Q R)) :=
  firstParam A B C F (compose A C E F Q R) τ

example (τ : BimoduleParamTrans A C E K Q Q') :
    BimoduleParamTrans A B F K (compose A B E F (compose A B C E P Q) R)
      (compose A B E F (compose A B C E P Q') R) :=
  firstParam A B E F R (secondParam A B C E P τ)

example (τ : BimoduleParamTrans A C E K Q Q') :
    BimoduleParamTrans A B F K (compose A B C F P (compose A C E F Q R))
      (compose A B C F P (compose A C E F Q' R)) :=
  secondParam A B C F P (firstParam A C E F R τ)

example (τ : BimoduleParamTrans A E F K R R') :
    BimoduleParamTrans A B F K (compose A B E F (compose A B C E P Q) R)
      (compose A B E F (compose A B C E P Q) R') :=
  secondParam A B E F (compose A B C E P Q) τ

example (τ : BimoduleParamTrans A E F K R R') :
    BimoduleParamTrans A B F K (compose A B C F P (compose A C E F Q R))
      (compose A B C F P (compose A C E F Q R')) :=
  secondParam A B C F P (secondParam A C E F Q τ)

example {K : Complex (ZMod 2)}
    {P P' : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}}
    (Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (τ : BimoduleParamTrans (ZMod 2) PUnit.{1} PUnit.{1} K P P') :
    BimoduleParamTrans (ZMod 2) PUnit.{1} PUnit.{1} K
      (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q)
      (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P' Q) :=
  firstParam (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} Q τ

#print axioms SerrePositivity.DifferentialGraded.Bimodule.leftParamNaturality_of_cochain
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramFamilyTrans
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramFamilyTrans_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.param_rightAction_units_smul
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.param_leftAction_units_smul
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.param_element_units_smul_left
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamHom_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamHom_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamHom_left_cochain
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamHom_left_cochain
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamHom_right_cochain
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamHom_right_cochain
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamRightAt
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamRightAt
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParam_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParam_value
