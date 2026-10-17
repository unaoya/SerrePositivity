module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionCounitNaturality
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionInsertion
public import Mathlib.Data.ZMod.Basic

/-! # graph延長の評価・余単位・挿入の独立宇宙と公理監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

example : moduleRestriction A D E F.op ⋙ (dgModuleExtension A D E F).onClosed ⟶
    𝟭 (ModuleCategory A E) := dgModuleCounit A D E F

example (M : RightModule A E) (d : D) :
    functorExtensionInsertionComponent A D E F (restrictModule A D E F.op M) d ≫
      functorExtensionEvaluationComponent A D E F M (F.obj d) = 𝟙 _ :=
  functorExtensionInsertion_evaluation A D E F M d

-- source/target宇宙は独立。非有界性・元のHomのflatnessに仮定を置かない。
example (M : RightModule A E) (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op (F.obj d))).X r) (h : GradedHom A e (F.obj d) s) (hn : r + s = n) :
    (functorExtensionEvaluationComponent A D E F M e).f n
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt e) d m h hn) =
      (r * s).negOnePow • moduleAction A M h m hn :=
  functorExtensionEvaluation_element A D E F M e d m h hn

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) :
    moduleRestriction (ZMod 2) X Y F.op ⋙ (dgModuleExtension (ZMod 2) X Y F).onClosed ⟶
      𝟭 (ModuleCategory (ZMod 2) Y) := dgModuleCounit (ZMod 2) X Y F

#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.rightAction_restrict
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.leftAction_restrict
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.restrictFamily
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.ι_restrictFamily_desc
#print axioms SerrePositivity.DifferentialGraded.functorGraph_leftAction
#print axioms SerrePositivity.DifferentialGraded.functorExtensionEvaluationFamily
#print axioms SerrePositivity.DifferentialGraded.functorExtensionEvaluationComponent
#print axioms SerrePositivity.DifferentialGraded.ι_functorExtensionEvaluationComponent
#print axioms SerrePositivity.DifferentialGraded.functorExtensionEvaluation_element
#print axioms SerrePositivity.DifferentialGraded.dgModuleExtension_action_element
#print axioms SerrePositivity.DifferentialGraded.functorExtensionEvaluation_action
#print axioms SerrePositivity.DifferentialGraded.functorExtensionEvaluation_naturality
#print axioms SerrePositivity.DifferentialGraded.functorExtensionCounit
#print axioms SerrePositivity.DifferentialGraded.functorExtensionCounit_eval
#print axioms SerrePositivity.DifferentialGraded.dgModuleCounit
#print axioms SerrePositivity.DifferentialGraded.functorExtensionInsertionComponent
#print axioms SerrePositivity.DifferentialGraded.functorExtensionInsertion_apply
#print axioms SerrePositivity.DifferentialGraded.functorExtensionInsertion_evaluation
#print axioms SerrePositivity.DifferentialGraded.dgModuleExtension_map_π
#print axioms SerrePositivity.DifferentialGraded.dgModuleExtension_map_eval
#print axioms SerrePositivity.DifferentialGraded.dgModuleExtension_map_eval_element
