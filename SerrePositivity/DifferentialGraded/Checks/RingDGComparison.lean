module
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # 非有界複体と一対象Aの右dg加群の準同値の検査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : QuasiEquivalence (ringConstantDG A) := ringConstantDG_quasiEquivalence A
example : QuasiEquivalence (moduleEvaluationDG A PUnit.{1} PUnit.unit) :=
  ringEvaluationDG_quasiEquivalence A
example (P Q : Complex A) : IsIso ((ringConstantDG A).map P Q) := by
  change IsIso (ringConstantHomIso A P Q).inv
  infer_instance
example : DGFunctor.comp (ringConstantDG A)
    (moduleEvaluationDG A PUnit.{1} PUnit.unit) = DGFunctor.id (A := A) (Complex A) :=
  ringConstantDG_comp_evaluation A
example : QuasiEquivalence (ringConstantDG (ZMod 2)) :=
  ringConstantDG_quasiEquivalence (ZMod 2)
example : QuasiEquivalence (moduleEvaluationDG (ZMod 2) PUnit.{1} PUnit.unit) :=
  ringEvaluationDG_quasiEquivalence (ZMod 2)

#print axioms ringConstantHomInv_identity
#print axioms ringConstantHomInv_comp
#print axioms ringConstantDG
#print axioms ringConstantDG_comp_evaluation
#print axioms ringConstantDGHomotopyEssSurj
#print axioms ringConstantDG_quasiEquivalence
#print axioms ringEvaluationDGHomotopyEssSurj
#print axioms ringEvaluationDG_quasiEquivalence
