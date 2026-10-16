module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import Mathlib.Data.ZMod.Basic

/-! # 外側両作用の全Hom自然性とbimodule合成双関手の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

example : BimoduleCategory A B C × BimoduleCategory A C E ⥤ BimoduleCategory A B E :=
  composeFunctor A B C E
example {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map (composeMap A B C E f g) =
      composeValueMap A B C E f g b e := composeMap_value_eval A B C E f g b e
example {P P' P'' : BimoduleCategory A B C} {Q Q' Q'' : BimoduleCategory A C E}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    composeMap A B C E (f ≫ f') (g ≫ g') =
      composeMap A B C E f g ≫ composeMap A B C E f' g' :=
  composeMap_comp A B C E f f' g g'

example {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q')
    (b b' : Bᵒᵖ) (c : C) (e : E)
    (u : GradedHom A b b' (-1))
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X 1)
    (v : ((BimoduleCategory.underlying A B C P).value b.unop c).X 0) :
    composeMapComponent A B C E f g b'.unop e 0
      (moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)).rightAt e) u
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b.unop) c (n := 1) q v
          (by decide)) (by decide)) =
    moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e) u
      (composeMapComponent A B C E f g b.unop e 1
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b.unop) c (n := 1) q v
          (by decide))) (by decide) :=
  composeMapComponent_rightAction_element A B C E f g b b' c e (j := -1)
    (by decide) (by decide) (by decide) u q v

example : BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1} ×
    BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1} ⥤
      BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1} :=
  composeFunctor (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}

#print axioms SerrePositivity.DifferentialGraded.hom_naturality_apply
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.valueMap_leftAction
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.valueMap_rightAction
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent_eq
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent_units_smul
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent_leftAction_element
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.composeMapComponent_rightAction_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueHom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueHom_apply
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueHom_eq
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueHom_right_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueHom_left_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeRightMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeRightMap_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeRightMap_component
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeRightMap_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.value_hom_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_value_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_id
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_comp
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor
