module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueElements
public import Mathlib.Data.ZMod.Basic

/-! # bimodule左右評価・相対tensorの両変数map・斉次生成元の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

example (b : B) : BimoduleCategory A B C ⥤ LeftModuleCategory A C :=
  BimoduleCategory.leftEvaluation A B C b
example (b : B) (e : E) :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ Complex A := valueFunctor A B C E b e
example (P P' : BimoduleCategory A B C) (f : P ⟶ P') (b : B) (c : C) :
    (leftModuleEvaluation A C c).map ((BimoduleCategory.leftEvaluation A B C b).map f) =
      (BimoduleCategory.valueEvaluation A B C b c).map f :=
  BimoduleCategory.leftEvaluation_map_eval A B C f b c

example (P P' Q Q' : BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1})
    (f : P ⟶ P') (g : Q ⟶ Q') (b c e : PUnit.{1})
    (m : ((BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} Q).value c e).X (-1))
    (t : ((BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} P).value b c).X 1) :
    (composeValueMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} f g b e).f 0
      (BalancedTensor.element (ZMod 2) PUnit.{1}
        ((BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} Q).rightAt e)
        ((BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} P).leftAt b)
        c m t (by decide : (-1 : ℤ) + 1 = 0)) =
    BalancedTensor.element (ZMod 2) PUnit.{1}
      ((BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} Q').rightAt e)
      ((BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} P').leftAt b) c
      (((BimoduleCategory.valueEvaluation (ZMod 2) PUnit.{1} PUnit.{1} c e).map g).f (-1) m)
      (((BimoduleCategory.valueEvaluation (ZMod 2) PUnit.{1} PUnit.{1} b c).map f).f 1 t)
      (by decide) :=
  composeValueMap_element (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} f g b c e m t (by decide)

#check composeValueMap_id
#check composeValueMap_comp

#print axioms SerrePositivity.DifferentialGraded.leftFamily_rightOpposite_naturality
#print axioms SerrePositivity.DifferentialGraded.leftModuleMorphismMk
#print axioms SerrePositivity.DifferentialGraded.leftModuleMorphismMk_eval
#print axioms SerrePositivity.DifferentialGraded.leftModuleMorphism_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.valueMap_left_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.leftEvaluation
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.leftEvaluation_map_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.ι_composeValueMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap_id
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap_comp
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.valueFunctor
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap_element
