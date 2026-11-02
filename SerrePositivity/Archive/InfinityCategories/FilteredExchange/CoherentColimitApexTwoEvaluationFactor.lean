module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastEvaluationFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomTwoMorphismEvaluation
/-!
概要：元の零面値と raw 二辺値全体を、元の二射の評価比較の合成へ戻す。
方針：同じ実中間係数を経由する因子式と、元の二評価の実頂点を照合する。
規約：元の零面値・raw 二辺値・全初期係数を保持する。
使われ方：Ncomp の元の二射評価の合成則への帰着。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂)
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor g

/-- 概要：同じ元の零面値と raw 二辺値。方針：同じ実終点で合成。規約：全係数を保持。使われ方：Ncomp。 -/
def coherentColimitApexZeroCompositeValue :=
  coherentColimitApexZeroValueAt B T ≪≫ coherentColimitApexCompositeValueComposite B T
/-- 概要：同じ最後・第一の実評価の合成。方針：元の中間値で合成。規約：指定値を保持。使われ方：二射評価。 -/
def coherentColimitApexTwoEvaluationComposite :=
  coherentColimitApexLastEvaluationComparison B T ≪≫
    coherentColimitApexMiddleFirstValueAfterLast B T
/-- 概要：元の零面と二辺値は元の二実評価。方針：中間因子を貼る。規約：指定値を保持。使われ方：Ncomp。 -/
lemma coherentColimitApexZeroCompositeValue_heq_two_actual :
    HEq (coherentColimitApexZeroCompositeValue B T)
      (coherentColimitApexTwoEvaluationComposite B T) := by
  have h := vertexIso_trans_heq_of_heq (coherentColimitApexZeroValueAt B T)
    (coherentColimitApexCompositeValueComposite B T) (coherentColimitApexZeroValueAt B T)
    (coherentColimitApexCompositeValueThroughMiddle B T) rfl rfl rfl (HEq.rfl)
    (coherentColimitApexCompositeValueComposite_heq_through_middle B T)
  have he : coherentColimitApexZeroValueAt B T ≪≫
      coherentColimitApexCompositeValueThroughMiddle B T =
      coherentColimitApexTwoEvaluationComposite B T := by
    unfold coherentColimitApexCompositeValueThroughMiddle coherentColimitApexTwoEvaluationComposite
      coherentColimitApexLastEvaluationComparison coherentColimitApexZeroLastMiddleValue
    simp only [Iso.trans_assoc]
  exact h.trans (heq_of_eq he)
/-- 概要：同じ実二評価は元の二射の指定評価。方針：三実頂点を照合。規約：全係数を保持。使われ方：合成則。 -/
lemma coherentColimitApexTwoEvaluationComposite_heq_canonical :
    HEq (coherentColimitApexTwoEvaluationComposite B T)
      (pointedHomTwoMorphismEvaluationComparison f g) := by
  have ha := coherentColimitApexZeroLastValue_source_vertex B T
  have hb := coherentColimitApexLastMiddleRatio_action_source_vertex B T
  have hc := congrArg (fun z => NatTrans.app ((ihom A).map ug) (Opposite.op ⦋0⦌) z)
    (coherentColimitApexFirstValue_action_source_vertex B T)
  exact vertexIso_trans_heq_of_heq (coherentColimitApexLastEvaluationComparison B T)
    (coherentColimitApexMiddleFirstValueAfterLast B T)
    (VertexIso.map (pointedHomMorphismEvaluationComparison g) ((pre P).app Y))
    (VertexIso.map (pointedHomMorphismEvaluationComparison f) ((ihom A).map ug))
    ha hb hc (coherentColimitApexLastEvaluationComparison_heq_pre_action B T)
    (coherentColimitApexMiddleFirstValueAfterLast_heq_evaluation B T)
/-- 概要：元の零面と raw 二辺値は元の二評価の合成。方針：同じ値照合を合成。規約：全係数を保持。使われ方：Ncomp。 -/
lemma coherentColimitApexZeroCompositeValue_heq_two_evaluation :
    HEq (coherentColimitApexZeroCompositeValue B T)
      (pointedHomTwoMorphismEvaluationComparison f g) :=
  (coherentColimitApexZeroCompositeValue_heq_two_actual B T).trans
    (coherentColimitApexTwoEvaluationComposite_heq_canonical B T)
end
end SerrePositivity.InfinityCategories.F2
