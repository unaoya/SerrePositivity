module
public import SerrePositivity.DifferentialGraded.Quotient.EvaluationPrefix
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluationPrepend

/-! # 非空path評価の微分を先頭消去と後方微分へ分ける -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 前方評価を保持して後方の任意次数cochainを合成する。 -/
def pathEvaluationTail (C : ContractedFunctor A D S E) (b : S) (w : Word S)
    (x y : D) (p : ℤ)
    (f : Cochain (term A D w b.val y)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)) p) :
    Cochain (term A D (b :: w) x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) p :=
  ((tensorLeftHom (homObject A D x b.val)
    (epsilonComplex A ⊗ term A D w b.val y)
    (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f p
    ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f p f)).comp
    (evaluationPrefixAction A C b x y) (add_zero p)

lemma pathEvaluation_cons_differential (C : ContractedFunctor A D S E)
    (b : S) (w : Word S) (x y : D) :
    δ 0 1 (pathEvaluation A C (b :: w) x y) =
    (eraseFirst A D b w x y).comp (pathEvaluation A C w x y) (add_zero 1) +
    pathEvaluationTail A C b w x y 1 (δ 0 1 (pathEvaluation A C w b.val y)) := by
  rw [pathEvaluation_cons_action, evaluationPrefixAction_evaluation_differential,
    ← pathEvaluation_prepend, ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
