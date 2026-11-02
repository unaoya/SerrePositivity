module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Data.ZMod.Basic

/-! # U10d1：一対象環と既存導来圏の同値・局所化・整合的shift -/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
example : DerivedModuleCategory A PUnit.{1} ≌ DerivedCategory (ModuleCat A) :=
  ringDerivedEquivalence A
example : (moduleDerivedEvaluation A PUnit.{1} PUnit.unit).IsEquivalence := inferInstance
example : HasShift (DerivedModuleCategory A PUnit.{1}) ℤ := inferInstance
example : (moduleToDerived A PUnit.{1}).CommShift ℤ := inferInstance
example : (ringDerivedEquivalence A).functor.CommShift ℤ := inferInstance
example : NatTrans.CommShift (ringDerivedEquivalence_fac A).hom ℤ := inferInstance
example : moduleToDerived A PUnit.{1} ⋙ (ringDerivedEquivalence A).functor ≅
    (ringModuleEquivalence A).functor ⋙ DerivedCategory.Q := ringDerivedEquivalence_fac A
section
local instance : HasDerivedCategory.{1} (ModuleCat.{0} ℤ) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (ModuleCat.{0} (ZMod 2)) := HasDerivedCategory.standard _
example : DerivedModuleCategory ℤ PUnit.{1} ≌ DerivedCategory (ModuleCat ℤ) :=
  ringDerivedEquivalence ℤ
example : DerivedModuleCategory (ZMod 2) PUnit.{1} ≌ DerivedCategory (ModuleCat (ZMod 2)) :=
  ringDerivedEquivalence (ZMod 2)
end
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationToDerivedCommShift
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedEvaluationLifting
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedEvaluationCommShift
#print axioms SerrePositivity.DifferentialGraded.moduleDerivedEvaluationFacCommShift
#print axioms SerrePositivity.DifferentialGraded.ringModuleQuasiIso_iff
#print axioms SerrePositivity.DifferentialGraded.ringModuleLocalizer
#print axioms SerrePositivity.DifferentialGraded.ringModuleLocalizerIsInduced
#print axioms SerrePositivity.DifferentialGraded.ringModuleLocalizerFunctorIsEquivalence
#print axioms SerrePositivity.DifferentialGraded.ringModuleLocalizerIsLocalizedEquivalence
#print axioms SerrePositivity.DifferentialGraded.ringDerivedEvaluationIsEquivalence
#print axioms SerrePositivity.DifferentialGraded.ringDerivedEquivalence
#print axioms SerrePositivity.DifferentialGraded.ringDerivedEquivalence_fac
#print axioms SerrePositivity.DifferentialGraded.ringModuleEquivalenceCommShift
#print axioms SerrePositivity.DifferentialGraded.ringDerivedEquivalenceCommShift
#print axioms SerrePositivity.DifferentialGraded.ringDerivedEquivalenceFacCommShift
