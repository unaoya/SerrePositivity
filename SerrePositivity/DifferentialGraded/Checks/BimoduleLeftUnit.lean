module
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import Mathlib.Data.ZMod.Basic

/-! # 対角bimoduleとの左単位比較の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example (P : Bimodule A B C) (c : C) :
    ForgetEnrichment.of (Complex A)
      ((BimoduleTensor.compose A B B C (Bimodule.diagonal A B) P).rightAt c) ≅
    ForgetEnrichment.of (Complex A) (P.rightAt c) := BimoduleTensor.leftUnitIso A B C P c
example (P : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    ForgetEnrichment.of (Complex (ZMod 2))
      ((BimoduleTensor.compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
        (Bimodule.diagonal (ZMod 2) PUnit.{1}) P).rightAt PUnit.unit) ≅
    ForgetEnrichment.of (Complex (ZMod 2)) (P.rightAt PUnit.unit) :=
  BimoduleTensor.leftUnitIso (ZMod 2) PUnit.{1} PUnit.{1} P PUnit.unit

#print axioms BalancedTensor.changeLeft
#print axioms BalancedTensor.ι_changeLeft_hom
#print axioms BalancedTensor.element_postcompose
#print axioms BalancedTensor.homMap_post_pre_eq
#print axioms Bimodule.diagonal_transpose_element
#print axioms BimoduleTensor.leftUnitValueIso
#print axioms BimoduleTensor.ι_leftUnitValueIso_hom
#print axioms BimoduleTensor.leftUnitValueIso_hom_element
#print axioms BimoduleTensor.leftUnitValueHom
#print axioms BimoduleTensor.leftUnitValueHom_element
#print axioms BimoduleTensor.leftUnitValue_naturality
#print axioms BimoduleTensor.leftUnitIso

#print axioms moduleAction_signed_representable
#print axioms BalancedTensor.leftUnitValueIso
#print axioms BalancedTensor.ι_leftUnitValueIso_hom
#print axioms BalancedTensor.leftUnitValueIso_hom_element
#print axioms BalancedTensor.leftUnitValueHom
#print axioms BalancedTensor.leftUnitValueHom_element
#print axioms BalancedTensor.diagonalTensorHomMap
#print axioms BalancedTensor.diagonalTensorHomMap_element
#print axioms BalancedTensor.leftUnitValue_element_naturality_of_evaluation
#print axioms BalancedTensor.leftUnitValue_element_naturality
#print axioms BalancedTensor.leftUnitValue_naturality
#print axioms BalancedTensor.leftYoneda_changeLeft_enriched_naturality
#print axioms BalancedTensor.leftUnitValueHom_enriched_naturality
#print axioms BimoduleTensor.leftUnitIso_hom_eval
#print axioms BimoduleTensor.leftUnitIso_inv_eval
#print axioms BimoduleTensor.leftUnitIso_hom_component
#print axioms BimoduleTensor.leftUnitValue_left_naturality
#print axioms BimoduleTensor.leftUnitIso_naturality
