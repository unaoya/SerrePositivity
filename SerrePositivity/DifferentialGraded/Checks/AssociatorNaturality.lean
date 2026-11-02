module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import Mathlib.Data.ZMod.Basic

/-! # 閉零bimodule射の三変数に関する結合自然同型の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example : leftTripleFunctor A B C E F ≅ rightTripleFunctor A B C E F :=
  associatorNatIso A B C E F
example (X : (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F) :
    (associatorNatIso A B C E F).app X =
      associatorIso A B C E F (BimoduleCategory.underlying A B C X.1.1)
        (BimoduleCategory.underlying A C E X.1.2) (BimoduleCategory.underlying A E F X.2) :=
  associatorNatIso_app A B C E F X
example {X Y : (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F}
    (f : X ⟶ Y) :
    (leftTripleFunctor A B C E F).map f ≫ (associatorNatIso A B C E F).hom.app Y =
      (associatorNatIso A B C E F).hom.app X ≫ (rightTripleFunctor A B C E F).map f :=
  (associatorNatIso A B C E F).hom.naturality f

example : leftTripleFunctor (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} ≅
    rightTripleFunctor (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} :=
  associatorNatIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}

#check leftTripleMap_element
#check rightTripleMap_element
#check associatorValue_map_naturality
#check associatorIso_naturality

#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftTripleFunctor
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightTripleFunctor
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftTripleMap_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightTripleMap_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftTripleComponent_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightTripleComponent_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorComponent_map_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom_map_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValue_map_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_hom_value_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_inv_value_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorNatIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorNatIso_app
