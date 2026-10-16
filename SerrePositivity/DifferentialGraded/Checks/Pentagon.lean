module
public import SerrePositivity.DifferentialGraded.Tensor.Pentagon
public import Mathlib.Data.ZMod.Basic

/-! # 四重合成の五角と生成元計算の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t x
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

example (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G) :
    (associatorIso A B E F G (compose A B C E P Q) R S).hom ≫
      (associatorIso A B C E G P Q (compose A E F G R S)).hom =
    composeMap A B F G (associatorIso A B C E F P Q R).hom
      (𝟙 (BimoduleCategory.of A F G S)) ≫
      (associatorIso A B C F G P (compose A C E F Q R) S).hom ≫
      composeMap A B C G (𝟙 (BimoduleCategory.of A B C P))
        (associatorIso A C E F G Q R S).hom :=
  pentagon A B C E F G P Q R S

example (P Q R S : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} (compose (ZMod 2) PUnit.{1}
      PUnit.{1} PUnit.{1} P Q) R S).hom ≫
      (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q (compose (ZMod 2)
      PUnit.{1} PUnit.{1} PUnit.{1} R S)).hom =
    composeMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} (associatorIso (ZMod 2) PUnit.{1} PUnit.{1}
      PUnit.{1} PUnit.{1} P Q R).hom
      (𝟙 (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1} S)) ≫
      (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P (compose (ZMod 2)
      PUnit.{1} PUnit.{1} PUnit.{1} Q R) S).hom ≫
      composeMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} (𝟙 (BimoduleCategory.of (ZMod 2) PUnit.{1}
      PUnit.{1} P))
        (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} Q R S).hom :=
  pentagon (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R S

#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.valueMap_id_apply
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorLeft_degree_element_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.quadLeftElement
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.quadRightElement
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.quadMiddleElement
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.quadLeft_cochain_element_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagonShort_component_element
#print axioms
      SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent_element_of_values
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_hom_value_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagonLongFirst_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagonLongThird_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagonLong_component_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagonValueHom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagonValue
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.pentagon
