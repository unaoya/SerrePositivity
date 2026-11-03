module
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 左加群の全Hom豊穣圏と実際の射の作用可換性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : DGCategory A (LeftModule A D) := inferInstance
example (x : D) : LeftModuleCategory A D ⥤ Complex A := leftModuleEvaluation A D x
#print axioms leftModuleHom
#print axioms leftModuleEnrichment
#print axioms LeftModuleCategory
#print axioms leftModuleToRightOppositeDG
#print axioms leftModuleToRightOpposite
#print axioms leftModuleEvaluationDG
#print axioms leftModuleEvaluation
#print axioms leftModuleClosedHomEquiv
#print axioms leftModuleEvaluation_map
#print axioms leftModuleMorphism_action_chain
