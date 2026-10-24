module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexZeroLastMiddleValue
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLastValueVertices
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomMorphismEvaluationPreAction
/-!
概要：元の零面値・最後指定対角値・中間の比の逆を、元の最後射の評価比較へ戻す。
方針：同じ三実頂点と二指定因子を保持して最後射評価の前作用へ照合する。
規約：全初期係数・実辺・零面値と比を保持する。
使われ方：Ncomp の元の二射評価の合成。
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
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "C" => pointedCoherentFiberComparison K₁ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₁)))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂)
local notation "R" => FunctorIso.precomp (coherentColimitApexLastRawValueRatio B T)
  (coherentColimitApexMiddleCoefficientMap B T)
local notation "N" => coherentColimitApexZeroLastMiddleValue B T
local notation "M" => VertexIso.map
  (VertexIso.map (pointedValueHomActionAt g) (NatTrans.app (pre C) Y))
    (NatTrans.app (pre P) Y)
/-- 概要：元の零面・最後対角値から同じ中間の比を除いた比較。
方針：同じ指定二因子を保持。規約：元の全係数と零面値を保持。
使われ方：最後射の元の評価比較の回収。 -/
def coherentColimitApexLastEvaluationComparison := N ≪≫ (R).symm
/-- 概要：同じ指定二因子は元の最後射の評価比較の第一射係数作用像。
方針：元の三実頂点を照合して二因子を合成する。
規約：全係数と指定値を保持。使われ方：元の二射評価の合成。 -/
lemma coherentColimitApexLastEvaluationComparison_heq_pre_action :
    HEq (coherentColimitApexLastEvaluationComparison B T)
      (VertexIso.map (pointedHomMorphismEvaluationComparison g) ((pre P).app Y)) := by
  have ha := coherentColimitApexZeroLastValue_source_vertex B T
  have hb := coherentColimitApexLastMiddleRatio_action_target_vertex B T
  have hc := coherentColimitApexLastMiddleRatio_action_source_vertex B T
  have hr := coherentColimitApexLastRawValueRatio_middle_heq_pre_action B T
  have hs := vertexIso_symm_heq_of_heq R M hc hb hr
  have he := vertexIso_trans_heq_of_heq N (R).symm
    (VertexIso.map (pointedHomMorphismValueComparison g) ((pre P).app Y)) (M).symm
    ha hb hc (coherentColimitApexZeroLastMiddleValue_heq_morphism_pre_action B T) hs
  exact he.trans (heq_of_eq (pointedHomMorphismEvaluationComparison_map_pre_eq_factors g P).symm)
end
end SerrePositivity.InfinityCategories.F2
