module
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U9a：指定quasiIsoの局所化、宇宙、普遍性・評価の受入入口 -/
@[expose] public section
noncomputable section
universe u v w w' z
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : Type (max (u + 1) v) := DerivedModuleCategory A D
example : Category.{max (u + 1) v} (DerivedModuleCategory A D) := inferInstance
example : Category.{max (u + 1) v} (HomotopyDerivedModuleCategory A D) := inferInstance
example : (moduleToDerived A D).IsLocalization (moduleQuasiIso A D) := inferInstance
example : (moduleHomotopyToDerived A D).IsLocalization (moduleHomotopyQuasiIso A D) := inferInstance
example : (moduleQuasiIso A D).HasLocalization.{max (u + 1) v} := moduleStandardLocalization A D
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso ((moduleToDerived A D).map f) ↔ moduleQuasiIso A D f :=
  moduleToDerived_map_isIso_iff A D f
example {M N : ModuleCategory ℤ PUnit.{1}} (f : M ⟶ N) :
    IsIso ((moduleToDerived ℤ PUnit.{1}).map f) ↔ moduleQuasiIso ℤ PUnit.{1} f :=
  moduleToDerived_map_isIso_iff ℤ PUnit.{1} f
example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) :
    IsIso ((moduleToDerived (ZMod 2) PUnit.{1}).map f) ↔ moduleQuasiIso (ZMod 2) PUnit.{1} f :=
  moduleToDerived_map_isIso_iff (ZMod 2) PUnit.{1} f

variable {E : Type w} [Category.{w'} E]
example (F : ModuleCategory A D ⥤ E) (hF : (moduleQuasiIso A D).IsInvertedBy F) :
    moduleToDerived A D ⋙ moduleDerivedLift A D F hF = F := moduleDerivedLift_fac A D F hF
example (F G : DerivedModuleCategory A D ⥤ E)
    (h : moduleToDerived A D ⋙ F = moduleToDerived A D ⋙ G) : F = G :=
  moduleDerivedLift_unique A D F G h
example : (DerivedModuleCategory A D ⥤ E) ≌ (moduleQuasiIso A D).FunctorsInverting E :=
  moduleDerivedUniversalEquivalence A D E
example [HasDerivedCategory.{z} (ModuleCat.{u} A)] (x : D) :
    moduleToDerived A D ⋙ moduleDerivedEvaluation A D x = moduleEvaluationToDerived A D x :=
  moduleDerivedEvaluation_fac A D x
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.DerivedModuleCategory
#print axioms SerrePositivity.DifferentialGraded.moduleToDerived
#print axioms SerrePositivity.DifferentialGraded.HomotopyDerivedModuleCategory
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyToDerived
#print axioms SerrePositivity.DifferentialGraded.moduleStandardLocalization
#print axioms SerrePositivity.DifferentialGraded.moduleToDerived_inverts
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyToDerived_inverts
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedIso
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedLift
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedLift_fac
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedLift_unique
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedNatTrans_ext
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedUniversalEquivalence
#print axioms SerrePositivity.DifferentialGraded.moduleHomology
#print axioms SerrePositivity.DifferentialGraded.moduleHomology_inverts
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedHomology
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedHomology_fac
#print axioms SerrePositivity.DifferentialGraded.moduleToDerived_map_isIso_iff
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationToDerived
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationToDerived_inverts
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedEvaluation
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedEvaluation_fac
