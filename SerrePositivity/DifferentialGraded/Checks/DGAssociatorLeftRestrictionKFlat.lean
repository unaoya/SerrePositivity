module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionModel
public import Mathlib.Data.ZMod.Basic

/-! # 固定右K-flat二因子の導来結合子と外側左制限の検査 -/
@[expose] public section
noncomputable section
universe v w z t s
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section CharacteristicTwo
variable (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
  (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
  (E : Type z) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type t) [DGCategory (ZMod 2) T] [Small.{0} T]
  (D : Type s) [DGCategory (ZMod 2) D] [Small.{0} D] (G : DGFunctor (ZMod 2) D T)
  (Q : RightKFlatBimoduleCategory (ZMod 2) C E)
  (R : RightKFlatBimoduleCategory (ZMod 2) E T)
local notation "LR" => Functor.obj (rightKFlatLeftRestriction (ZMod 2) E T D G) R
local notation "QR" => rightKFlatCompose (ZMod 2) C E T Q R
local notation "QLR" => rightKFlatCompose (ZMod 2) C E D Q LR
local notation "LQR" => Functor.obj (rightKFlatLeftRestriction (ZMod 2) C T D G) QR
local notation "L" => derivedBimoduleRestriction (ZMod 2) B D B T (DGFunctor.id B) G

-- 局所Hom K-flat性やGの準同値性を仮定せず、前因子は任意の導来対象。
theorem SerrePositivity.DifferentialGraded.Checks.associatorLeftRestrictionKFlat_charTwo_component
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    ((rightKFlatDerivedAssociator (ZMod 2) B C E D Q LR).hom ≫
      rightKFlatDerivedMap (ZMod 2) B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso (ZMod 2) C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso (ZMod 2) B C T D G QR).hom).app P =
    (whiskerLeft (rightKFlatDerivedCompose (ZMod 2) B C E Q)
        (derivedComposeWithLeftRestrictionIso (ZMod 2) B E T D G R).hom ≫
      whiskerRight (rightKFlatDerivedAssociator (ZMod 2) B C E T Q R).hom L).app P :=
  NatTrans.congr_app (rightKFlatDerivedAssociator_leftRestriction (ZMod 2) B C E T D G Q R) P
end CharacteristicTwo

#check derivedComposeWithLeftRestrictionIso_base_app
#check rightKFlatDerivedAssociator_leftRestriction
#print axioms derivedComposeWithLeftRestrictionIso_base_app
#print axioms rightKFlatDerivedAssociator_leftRestriction

#print axioms
  SerrePositivity.DifferentialGraded.Checks.associatorLeftRestrictionKFlat_charTwo_component

#check derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
#check derivedLeftRestriction_inner_model_square
#print axioms derivedBimoduleComposeLeftRestrictionIso_inv_model_square
#print axioms leftRestrictionDerivedComposeSourceBaseIso_hom_app
#print axioms leftRestrictionDerivedComposeTargetBaseIso_hom_app
#print axioms derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
#print axioms derivedLeftRestriction_inner_model_square

#check derivedLeftRestriction_nested_model_square
#print axioms derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation
#print axioms derivedLeftRestriction_nested_prefix_square
#print axioms derivedLeftRestriction_nested_model_square

#check derivedBimoduleAssociator_leftRestriction_rightKFlat (ZMod 2)
#print axioms derivedLeftRestriction_pair_model_square
#print axioms derivedBimoduleAssociator_leftRestriction_rightKFlat
