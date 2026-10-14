module
public import SerrePositivity.DifferentialGraded.Module.Zero
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U7a1：零加群・全次数零 Hom・objectwise 判定の受入と公理監査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits Opposite
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : HasZeroObject (ModuleCategory A D) := inferInstance
example (x : D) : (zeroModule A D).obj (op x) = (0 : Complex A) := rfl
example (M : ModuleCategory A D) :
    IsZero M ↔ ∀ x : D, IsZero ((moduleEvaluation A D x).obj M) :=
  module_isZero_iff A D M
example (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleZeroTo A D M) = 0 := moduleZeroTo_eval A D M x
example (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleToZero A D M) = 0 := moduleToZero_eval A D M x
example (x : D) : (moduleEvaluation A D x).obj (0 : ModuleCategory A D) ≅ (0 : Complex A) :=
  moduleEvaluationZeroIso A D x
example (M : RightModule A D) : IsZero (moduleHom A D (zeroModule A D) M) :=
  moduleHom_isZero_src A D _ M (fun _ => isZero_zero _)
example (M : RightModule A D) : IsZero (moduleHom A D M (zeroModule A D)) :=
  moduleHom_isZero_tgt A D M _ (fun _ => isZero_zero _)

example (P : Complex ℤ) (f : Homogeneous (0 : Complex ℤ) P (-1)) : f = 0 :=
  homogeneous_eq_zero_of_isZero_src (isZero_zero _) f
example (P : Complex ℤ) (f : Homogeneous P (0 : Complex ℤ) 1) : f = 0 :=
  homogeneous_eq_zero_of_isZero_tgt (isZero_zero _) f
example : IsZero (moduleZero (ZMod 2) PUnit.{1}) := moduleZero_isZero _ _
example : IsZero ((moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj (moduleZero ℤ PUnit.{1})) :=
  isZero_zero _
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.closedToComplexAdditive
#print axioms SerrePositivity.DifferentialGraded.homogeneous_eq_zero_of_isZero_src
#print axioms SerrePositivity.DifferentialGraded.homogeneous_eq_zero_of_isZero_tgt
#print axioms SerrePositivity.DifferentialGraded.homComplex_isZero_src
#print axioms SerrePositivity.DifferentialGraded.homComplex_isZero_tgt
#print axioms SerrePositivity.DifferentialGraded.zeroModule
#print axioms SerrePositivity.DifferentialGraded.moduleHom_isZero_src
#print axioms SerrePositivity.DifferentialGraded.moduleHom_isZero_tgt
#print axioms SerrePositivity.DifferentialGraded.moduleZeroTo
#print axioms SerrePositivity.DifferentialGraded.moduleToZero
#print axioms SerrePositivity.DifferentialGraded.moduleZeroTo_eval
#print axioms SerrePositivity.DifferentialGraded.moduleToZero_eval
#print axioms SerrePositivity.DifferentialGraded.moduleZero_isZero
#print axioms SerrePositivity.DifferentialGraded.moduleHasZeroObject
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationAdditive
#print axioms SerrePositivity.DifferentialGraded.module_isZero_iff
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationZeroIso
