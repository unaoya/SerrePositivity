module
public import SerrePositivity.DifferentialGraded.Tensor.Triangle
public import Mathlib.Data.ZMod.Basic

/-! # 全Hom自然な単位同型と閉零bimodule射の三角coherenceの受入監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

example (P : Bimodule A B C) :
    BimoduleCategory.of A B C (compose A B B C (Bimodule.diagonal A B) P) ≅
      BimoduleCategory.of A B C P := leftBimoduleUnitIso A B C P

variable [Small.{u} C] (E : Type z) [DGCategory A E]
example (P : Bimodule A B C) :
    BimoduleCategory.of A B C (compose A B C C P (Bimodule.diagonal A C)) ≅
      BimoduleCategory.of A B C P := rightBimoduleUnitIso A B C P
example (P : Bimodule A B C) (Q : Bimodule A C E) :
    composeMap A B C E (rightBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) =
    (associatorIso A B C C E P (Bimodule.diagonal A C) Q).hom ≫
      composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (leftBimoduleUnitIso A C E Q).hom := triangle A B C E P Q

example (P Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    composeMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
      (rightBimoduleUnitIso (ZMod 2) PUnit.{1} PUnit.{1} P).hom
      (𝟙 (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1} Q)) =
    (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
      P (Bimodule.diagonal (ZMod 2) PUnit.{1}) Q).hom ≫
    composeMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
      (𝟙 (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1} P))
      (leftBimoduleUnitIso (ZMod 2) PUnit.{1} PUnit.{1} Q).hom :=
  triangle (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q

#print axioms SerrePositivity.DifferentialGraded.tensorLeft_generator_map
#print axioms SerrePositivity.DifferentialGraded.tensorRight_generator_map
#print axioms SerrePositivity.DifferentialGraded.tensor_associator_balance
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso_hom_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso_inv_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso_hom_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso_inv_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.triangleLeft_ι
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.triangleRight_ι
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.triangleValue
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.triangle
