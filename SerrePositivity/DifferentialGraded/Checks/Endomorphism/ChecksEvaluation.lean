module
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import Mathlib.Data.ZMod.Basic

/-! # balanced評価とtensor–Hom単位・余単位の監査 -/
public section
noncomputable section
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded

example (E : Complex ℤ) : DGCategory ℤ (EndomorphismObject E) := inferInstance

example (E : Complex (ZMod 2)) : DGCategory (ZMod 2) (EndomorphismObject E) := inferInstance

example (E X Y : Complex ℤ) (m : GradedHom ℤ E Y (-1)) (t : GradedHom ℤ X E 1) :
    (endomorphismEvaluationComponent ℤ (Complex ℤ) E X Y).f 0
      (ιTensorObj (homObject ℤ (Complex ℤ) E Y) (homObject ℤ (Complex ℤ) X E)
        (-1) 1 0 (by omega) (m ⊗ₜ[ℤ] t)) =
      ((-1 : ℤ) * 1).negOnePow • forward ℤ t m (by omega) :=
  endomorphismEvaluationComponent_apply ℤ (Complex ℤ) E X Y m t (by omega)

#print axioms endomorphismEvaluationComponent
#print axioms endomorphismEvaluationComponent_apply
#print axioms endomorphismEvaluationFamily
#print axioms endomorphismEvaluation
#print axioms endomorphismEvaluation_ι
#print axioms endomorphismEvaluationMate
#print axioms endomorphismEvaluationMate_unit
#print axioms endomorphismEvaluation_counit
