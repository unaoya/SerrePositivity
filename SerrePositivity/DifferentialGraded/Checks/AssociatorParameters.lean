module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import Mathlib.Data.ZMod.Basic

/-! # 結合比較の任意パラメータ三変数自然性の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {K : Complex A}

-- Fのsmall性も、Kの閉性・有界性も要求しない。
example {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (R : Bimodule A E F) (τ : BimoduleParamTrans A B C K P P') (f : F) :
    (firstParam A B E F R (firstParam A B C E Q τ)).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P' Q) R).rightAt f)
        ((compose A B C F P' (compose A C E F Q R)).rightAt f)
        (associatorRightModuleIso A B C E F P' Q R f).hom =
    (firstParam A B C F (compose A C E F Q R) τ).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P' (compose A C E F Q R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom :=
  associator_firstParam A B C E F Q R τ f

example (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (R : Bimodule A E F) (τ : BimoduleParamTrans A C E K Q Q') (f : F) :
    (firstParam A B E F R (secondParam A B C E P τ)).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q') R).rightAt f)
        ((compose A B C F P (compose A C E F Q' R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q' R f).hom =
    (secondParam A B C F P (firstParam A C E F R τ)).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q' R)).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom :=
  associator_middleParam A B C E F P R τ f

example (P : Bimodule A B C) (Q : Bimodule A C E)
    {R R' : Bimodule A E F} (τ : BimoduleParamTrans A E F K R R') (f : F) :
    (secondParam A B E F (compose A B C E P Q) τ).app f ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q) R').rightAt f)
        ((compose A B C F P (compose A C E F Q R')).rightAt f)
        (associatorRightModuleIso A B C E F P Q R' f).hom =
    (secondParam A B C F P (secondParam A C E F Q τ)).app f ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q R')).rightAt f)
        (associatorRightModuleIso A B C E F P Q R f).hom :=
  associator_lastParam A B C E F P Q τ f

example {L : Complex (ZMod 2)} {P P' : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}} (Q : Bimodule (ZMod
      2) PUnit.{1} PUnit.{1})
    (R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (τ : BimoduleParamTrans (ZMod 2) PUnit.{1}
      PUnit.{1} L P P') (f : PUnit.{1}) :
    (firstParam (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} R (firstParam (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} Q τ)).app f ≫
      moduleHomPostcompose (ZMod 2) PUnit.{1}
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} P Q) R).rightAt f)
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} P' Q) R).rightAt f)
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P' (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} Q R)).rightAt f)
        (associatorRightModuleIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P' Q R f).hom =
    (firstParam (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} Q R) τ).app f ≫
      moduleHomPrecompose (ZMod 2) PUnit.{1}
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} P Q) R).rightAt f)
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} Q R)).rightAt f)
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P' (compose (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} Q R)).rightAt f)
        (associatorRightModuleIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R f).hom :=
  associator_firstParam (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} Q R τ f

#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorLeft_homMap_post_pre_eq
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.tripleFirstLeft_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.tripleFirstRight_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.tripleMiddleLeft_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.tripleMiddleRight_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.tripleLastLeft_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.tripleLastRight_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_firstParam_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_middleParam_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_lastParam_value
#print axioms SerrePositivity.DifferentialGraded.Bimodule.param_square_of_values
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_firstParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_middleParam
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_lastParam
