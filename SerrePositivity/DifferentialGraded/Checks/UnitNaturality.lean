module
public import SerrePositivity.DifferentialGraded.Tensor.UnitFunctors
public import Mathlib.Data.ZMod.Basic

/-! # 単位の閉零bimodule変数自然性と自然同型の受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

example : leftUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) := leftUnitNatIso A B C

example {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    composeMap A B B C (𝟙 (BimoduleCategory.of A B B (Bimodule.diagonal A B))) f ≫
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P')).hom =
    (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom ≫ f :=
  leftBimoduleUnitIso_naturality A B C f

variable [Small.{u} C]
example : rightUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) := rightUnitNatIso A B C

example {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    composeMap A B C C f (𝟙 (BimoduleCategory.of A C C (Bimodule.diagonal A C))) ≫
      (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P')).hom =
    (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom ≫ f :=
  rightBimoduleUnitIso_naturality A B C f

example : leftUnitFunctor (ZMod 2) PUnit.{1} PUnit.{1} ≅
    𝟭 (BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1}) :=
  leftUnitNatIso (ZMod 2) PUnit.{1} PUnit.{1}

example : rightUnitFunctor (ZMod 2) PUnit.{1} PUnit.{1} ≅
    𝟭 (BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1}) :=
  rightUnitNatIso (ZMod 2) PUnit.{1} PUnit.{1}

#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.leftUnitValueHom_map_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitValue_map_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitValue_map_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitFunctor
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitNatIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftUnitNatIso_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitFunctor
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitNatIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitNatIso_app
