module
public import SerrePositivity.DifferentialGraded.StageFour
public import Mathlib.Data.ZMod.Basic

/-! # U7c2：objectwise 余極限・全次数作用・普遍性・宇宙契約 -/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits Opposite Pretriangulated CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Category.{w'} J] (F : J ⥤ ModuleCategory A D)
variable [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)]
example : IsColimit (moduleColimitCocone A D F) := moduleColimitCoconeIsColimit A D F
example (x : D) : PreservesColimit F (moduleEvaluation A D x) := inferInstance
example [HasColimit F] (x : D) :
    (moduleEvaluation A D x).obj (colimit F) ≅ colimit (F ⋙ moduleEvaluation A D x) :=
  moduleEvaluationColimitIso A D F x
example (j : J) (x : D) :
    (moduleEvaluation A D x).map (moduleColimitι A D F j) =
      colimit.ι (F ⋙ moduleEvaluation A D x) j := moduleColimitι_eval A D F j x
example (s : Cocone F) (x : D) :
    (moduleEvaluation A D x).map (moduleColimitDesc A D F s) =
      moduleColimitDescValue A D F s (op x) := moduleColimitDesc_eval A D F s x
omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
example [Small.{u} J] : HasColimit F := inferInstance
omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
example : HasColimitsOfSize.{w', u} (ModuleCategory A D) := inferInstance
omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
example (x : D) : PreservesColimitsOfSize.{w', u} (moduleEvaluation A D x) := inferInstance
example (G : Discrete ℕ ⥤ ModuleCategory ℤ PUnit.{1}) : HasColimit G := inferInstance
example (G : Discrete ℕ ⥤ ModuleCategory (ZMod 2) PUnit.{1}) : HasColimit G := inferInstance
example (G : Discrete ℕ ⥤ ModuleCategory ℤ PUnit.{1}) :
    (moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj (colimit G) ≅
      colimit (G ⋙ moduleEvaluation ℤ PUnit.{1} PUnit.unit) := moduleEvaluationColimitIso _ _ _ _
example (M : ℕ → ModuleCategory ℤ PUnit.{1}) : HasCoproduct M := inferInstance
example {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).mapTriangle.obj (moduleConeTriangle A D f) ≅
      mappingCone.triangle ((moduleEvaluation A D x).map f) :=
  moduleConeTriangleEvaluationIso A D f x
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.homComplex_colimit_ext
#print axioms SerrePositivity.DifferentialGraded.moduleColimitValue
#print axioms SerrePositivity.DifferentialGraded.moduleColimitActionCocone
#print axioms SerrePositivity.DifferentialGraded.moduleColimitAction
#print axioms SerrePositivity.DifferentialGraded.moduleColimitAction_ι
#print axioms SerrePositivity.DifferentialGraded.moduleColimitHom
#print axioms SerrePositivity.DifferentialGraded.moduleColimitHom_ι
#print axioms SerrePositivity.DifferentialGraded.moduleColimitHom_ι_v
#print axioms SerrePositivity.DifferentialGraded.moduleColimitHom_id
#print axioms SerrePositivity.DifferentialGraded.moduleColimitHom_comp
#print axioms SerrePositivity.DifferentialGraded.colimitModule
#print axioms SerrePositivity.DifferentialGraded.moduleColimitObj
#print axioms SerrePositivity.DifferentialGraded.moduleColimitι
#print axioms SerrePositivity.DifferentialGraded.moduleColimitι_eval
#print axioms SerrePositivity.DifferentialGraded.moduleColimitCocone
#print axioms SerrePositivity.DifferentialGraded.moduleColimitDescValue
#print axioms SerrePositivity.DifferentialGraded.moduleColimitDescValue_ι
#print axioms SerrePositivity.DifferentialGraded.moduleColimitDescValue_action
#print axioms SerrePositivity.DifferentialGraded.moduleColimitDescValue_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleColimitDesc
#print axioms SerrePositivity.DifferentialGraded.moduleColimitDesc_eval
#print axioms SerrePositivity.DifferentialGraded.moduleColimitCoconeIsColimit
#print axioms SerrePositivity.DifferentialGraded.moduleHasColimit_of_evaluations
#print axioms SerrePositivity.DifferentialGraded.moduleColimitCoconeEvaluationIso
#print axioms SerrePositivity.DifferentialGraded.moduleColimitCoconeEvaluationIsColimit
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesColimit
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationColimitIso
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationColimitIso_ι_hom
#print axioms SerrePositivity.DifferentialGraded.moduleHasColimitsOfShape
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesColimitsOfShape
#print axioms SerrePositivity.DifferentialGraded.moduleHasColimitsOfSize
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesColimitsOfSize
