module
public import SerrePositivity.DifferentialGraded.Module.Limits
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U7c1：objectwise 極限・全次数作用・普遍性・宇宙契約 -/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Category.{w'} J] (F : J ⥤ ModuleCategory A D)
variable [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)]
example : IsLimit (moduleLimitCone A D F) := moduleLimitConeIsLimit A D F
example (x : D) : PreservesLimit F (moduleEvaluation A D x) := inferInstance
example [HasLimit F] (x : D) :
    (moduleEvaluation A D x).obj (limit F) ≅ limit (F ⋙ moduleEvaluation A D x) :=
  moduleEvaluationLimitIso A D F x
example (j : J) (x : D) :
    (moduleEvaluation A D x).map (moduleLimitπ A D F j) =
      limit.π (F ⋙ moduleEvaluation A D x) j := moduleLimitπ_eval A D F j x
example (s : Cone F) (x : D) :
    (moduleEvaluation A D x).map (moduleLimitLift A D F s) =
      moduleLimitLiftValue A D F s (op x) := moduleLimitLift_eval A D F s x
omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
example [Small.{u} J] : HasLimit F := inferInstance
omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
example : HasLimitsOfSize.{w', u} (ModuleCategory A D) := inferInstance
omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
example (x : D) : PreservesLimitsOfSize.{w', u} (moduleEvaluation A D x) := inferInstance
example (G : Discrete ℕ ⥤ ModuleCategory ℤ PUnit.{1}) : HasLimit G := inferInstance
example (G : Discrete ℕ ⥤ ModuleCategory (ZMod 2) PUnit.{1}) : HasLimit G := inferInstance
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.moduleActionChain
#print axioms SerrePositivity.DifferentialGraded.closedFamily_action_chain
#print axioms SerrePositivity.DifferentialGraded.moduleMorphism_action_chain
#print axioms SerrePositivity.DifferentialGraded.homComplex_limit_ext
#print axioms SerrePositivity.DifferentialGraded.identity_hom_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleLimitValue
#print axioms SerrePositivity.DifferentialGraded.moduleLimitActionCone
#print axioms SerrePositivity.DifferentialGraded.moduleLimitAction
#print axioms SerrePositivity.DifferentialGraded.moduleLimitAction_π
#print axioms SerrePositivity.DifferentialGraded.moduleLimitHom
#print axioms SerrePositivity.DifferentialGraded.moduleLimitHom_π
#print axioms SerrePositivity.DifferentialGraded.moduleLimitHom_π_v
#print axioms SerrePositivity.DifferentialGraded.moduleLimitHom_id
#print axioms SerrePositivity.DifferentialGraded.moduleLimitHom_comp
#print axioms SerrePositivity.DifferentialGraded.limitModule
#print axioms SerrePositivity.DifferentialGraded.moduleLimitObj
#print axioms SerrePositivity.DifferentialGraded.moduleLimitπ
#print axioms SerrePositivity.DifferentialGraded.moduleLimitπ_eval
#print axioms SerrePositivity.DifferentialGraded.moduleLimitCone
#print axioms SerrePositivity.DifferentialGraded.moduleLimitLiftValue
#print axioms SerrePositivity.DifferentialGraded.moduleLimitLiftValue_π
#print axioms SerrePositivity.DifferentialGraded.moduleLimitLiftValue_action
#print axioms SerrePositivity.DifferentialGraded.moduleLimitLiftValue_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleLimitLift
#print axioms SerrePositivity.DifferentialGraded.moduleLimitLift_eval
#print axioms SerrePositivity.DifferentialGraded.moduleLimitConeIsLimit
#print axioms SerrePositivity.DifferentialGraded.moduleHasLimit_of_evaluations
#print axioms SerrePositivity.DifferentialGraded.moduleLimitConeEvaluationIso
#print axioms SerrePositivity.DifferentialGraded.moduleLimitConeEvaluationIsLimit
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesLimit
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationLimitIso
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationLimitIso_hom_π
#print axioms SerrePositivity.DifferentialGraded.moduleHasLimitsOfShape
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesLimitsOfShape
#print axioms SerrePositivity.DifferentialGraded.moduleHasLimitsOfSize
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesLimitsOfSize
