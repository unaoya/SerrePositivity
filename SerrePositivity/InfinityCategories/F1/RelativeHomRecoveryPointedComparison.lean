module

public import SerrePositivity.InfinityCategories.F1.PointedRightHomEvaluation

/-!
概要：元の Kan 値の coherent recovery と実際の pointed recovery を比較する。
方針：全右 Hom の点評価比較を、表現対象の同じ相対恒等射へ制限する。
規約：既存の recovery の定義と標準 Hom 同値の逆を変更しない。
使われ方：元の主比較の充満忠実性と反対向きの往復の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の coherent recovery に同じ fiber 比較を続けると、実際の pointed recovery と同型。 -/
def relativeHomCoherentRecovery_pointedIso {B : SSet.{u}} (a q : LeftFibrationObject B) :
    FunctorIso (relativeHomCoherentPointedRecovery a q)
      (relativeHomCoherentRecovery a q ≫
        pointedRightFiberComparison ((relativeFunctorEnrichedEvaluation a.val).obj q)) := by
  have e := (pointedRightHomEvaluate_nativeIso (relativeHomIdentityKanObject q)
    ((relativeFunctorEnrichedEvaluation a.val).obj q) (relativeHomPointedIdentity q)).precomp
      (relativeHomCoherentEvaluationMap a q q)
  rw [relativeHomPointedIdentity_value] at e
  have n := relativeHomCoherentPointedRecovery_evaluateIso a q
  have h : FunctorIso
      (relativeHomCoherentEvaluationMap a q q ≫
        pointedRightHomEvaluate (relativeHomIdentityKanObject q)
          ((relativeFunctorEnrichedEvaluation a.val).obj q) (relativeHomPointedIdentity q))
      (relativeHomCoherentRecovery a q ≫
        pointedRightFiberComparison ((relativeFunctorEnrichedEvaluation a.val).obj q)) := by
    change FunctorIso _
      ((relativeHomCoherentEvaluationMap a q q ≫
        (coherentHomEquivalence (relativeHomIdentityKanObject q)
          ((relativeFunctorEnrichedEvaluation a.val).obj q)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (evaluateFunctorAt ((relativeFunctorIdentity q.val).app
            (Opposite.op ⦋0⦌) PUnit.unit))) ≫
        pointedRightFiberComparison ((relativeFunctorEnrichedEvaluation a.val).obj q))
    simpa only [Category.assoc] using e
  exact n ≪≫ h

/-- 元の Kan 値の coherent recovery そのものは、全 coherent 変換空間で同値。 -/
lemma relativeHomCoherentRecovery_isQCatEquivalence {B : SSet.{u}}
    (a q : LeftFibrationObject B) : IsQCatEquivalence (relativeHomCoherentRecovery a q) := by
  have h := (relativeHomCoherentPointedRecovery_isQCatEquivalence a q).ofFunctorIso
    (relativeHomCoherentRecovery_pointedIso a q)
  exact (pointedRightFiberComparison_isQCatEquivalence
    ((relativeFunctorEnrichedEvaluation a.val).obj q)).cancel_right h

/-- 元の相対 Hom から実際の coherent 変換空間への主比較そのものは同値。 -/
lemma relativeHomCoherentComparison_isQCatEquivalence {B : SSet.{u}}
    (a q : LeftFibrationObject B) : IsQCatEquivalence (relativeHomCoherentComparison a q) := by
  have h := (qCatEquivalenceOfIso (Iso.refl
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (relativeFunctorSpace q.val.hom a.val.hom)))).isQCatEquivalence.ofFunctorIso
        (relativeHomCoherentComparisonRecoveryIso a q).symm
  exact (relativeHomCoherentRecovery_isQCatEquivalence a q).cancel_right h

end SerrePositivity.InfinityCategories
