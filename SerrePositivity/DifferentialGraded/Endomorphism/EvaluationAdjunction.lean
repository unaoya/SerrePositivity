module
public import SerrePositivity.DifferentialGraded.Endomorphism.Evaluation

/-! # balanced合成評価と既存tensor–Hom随伴の比較

ここではHom(X,E)を固定した複体値の随伴を使う。
enhancement全体とEnd(E)加群の間の再構成随伴とは区別する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E : D)

/-- 評価のtensor–Hom転置は右End(E)加群の実際の閉零射である。 -/
def endomorphismEvaluationMate (X Y : D) :
    ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y) ⟶
      ForgetEnrichment.of (Complex A)
        (homRightModule A (EndomorphismObject E)
          (endomorphismHomLeft A D E X) (homObject A D X Y)) :=
  BalancedTensor.tensorHomEquiv A _ _ _ _ (endomorphismEvaluation A D E X Y)

/-- 単位との比較：評価の転置は既存随伴の単位と右随伴による評価の像の合成。 -/
lemma endomorphismEvaluationMate_unit (X Y : D) :
    endomorphismEvaluationMate A D E X Y =
      (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).unit.app
          (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y)) ≫
        (homRightFunctor A _ (endomorphismHomLeft A D E X)).map
          (endomorphismEvaluation A D E X Y) := by
  change BalancedTensor.tensorHomEquiv A _ _ _ _ _ = _
  rw [← BalancedTensor.tensorHomAdjunction_homEquiv]
  exact (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).homEquiv_unit _ _ _

/-- 余単位との比較：balanced評価はその転置をtensorして余単位で評価したもの。 -/
lemma endomorphismEvaluation_counit (X Y : D) :
    endomorphismEvaluation A D E X Y =
      (BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).map
          (endomorphismEvaluationMate A D E X Y) ≫
        (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).counit.app
          (homObject A D X Y) := by
  have h := (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).homEquiv_counit
    (g := endomorphismEvaluationMate A D E X Y)
  rw [BalancedTensor.tensorHomAdjunction_homEquiv] at h
  exact ((BalancedTensor.tensorHomEquiv A (EndomorphismObject E)
    (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))
    (endomorphismHomLeft A D E X) (homObject A D X Y)).symm_apply_apply
      (endomorphismEvaluation A D E X Y)).symm.trans h

end SerrePositivity.DifferentialGraded
