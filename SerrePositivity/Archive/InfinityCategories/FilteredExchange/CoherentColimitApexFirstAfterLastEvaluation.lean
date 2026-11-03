module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexCompositeValueLastFactors
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastRatioExchange
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexFirstEvaluationFactor
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoEdgeValuePostComposite
/-!
概要：元の中間比較に続く第一辺値を、元の第一射の評価比較の最後射への像へ戻す。
方針：元の中間比較と辺値を同時に後合成し、実両端を保って内部 Hom の像で読む。
規約：元の実中間・全初期係数・raw 第一辺値を保持する。
使われ方：Ncomp の元の二辺値の中間での貼り合わせ。
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
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "m" => coherentColimitApexMiddleCoefficientMap B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "uf" => CategoryTheory.Functor.map SSet.uliftFunctor
  (coherentEdgeHom (SpaceInfinity.δ 2 s))
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor
  (coherentEdgeHom (SpaceInfinity.δ 0 s))
local notation "R" => coherentColimitApexLastRawValueRatio B T

/-- 概要：元の中間比較と最後射へ写した raw 第一辺値の同じ合成。
方針：元の二因子を保持。規約：指定値を再選択しない。
使われ方：元の二辺値の中間因子。 -/
def coherentColimitApexMiddleFirstValueAfterLast :=
  (coherentColimitApexPointedMiddleEndpointIso B T).postcomp (R).sourceMap ≪≫
    coherentColimitApexFirstValueAfterLast B T
/-- 概要：同じ二因子は元の第一辺値合成の同じ後合成。
方針：同じ三端点の表示だけを揃える。規約：指定値を保持。
使われ方：第一射の評価への帰還。 -/
lemma coherentColimitApexMiddleFirstValueAfterLast_heq_first_post :
    HEq (coherentColimitApexMiddleFirstValueAfterLast B T)
      (FunctorIso.postcomp (coherentColimitApexFirstValueComposite B T) ug) := by
  exact functorIsoEdgeValuePostAt_comp_heq (coherentColimitRawFiberTransport B a)
    V₀ V₁ uf (coherentColimitApexRawFirstValueIso B T) q ug m
    (coherentColimitApexPointedMiddleEndpointIso B T)
/-- 概要：元の第一辺値合成の後合成は同じ評価比較の内部 Hom の像。
方針：明示した同じ二頂点を保って後合成する。
規約：全係数と指定値を保持。使われ方：二辺評価の合成。 -/
lemma coherentColimitApexFirstValueComposite_post_last_heq_evaluation :
    HEq (FunctorIso.postcomp (coherentColimitApexFirstValueComposite B T) ug)
      (VertexIso.map
        (pointedHomMorphismEvaluationComparison (coherentEdgeHom (SpaceInfinity.δ 2 s)))
        ((ihom (spaceSimplexPointedCoefficients s)).map ug)) := by
  refine functorIso_postcomp_heq_vertexMap_of_heq (coherentColimitApexFirstValueComposite B T)
    (pointedHomMorphismEvaluationComparison (coherentEdgeHom (SpaceInfinity.δ 2 s))) ?_ ?_
    (coherentColimitApexFirstValueComposite_heq_evaluation B T) ug
  · exact coherentColimitApexFirstValue_source_vertex B T
  · convert coherentColimitApexFirstValue_action_source_vertex B T using 1 <;> rfl
/-- 概要：元の中間比較と第一辺値は、同じ第一射の評価の最後射への像。
方針：同じ元の二照合を合成する。規約：全初期係数と指定値を保持。
使われ方：元の raw 二辺値を評価合成へ戻す。 -/
lemma coherentColimitApexMiddleFirstValueAfterLast_heq_evaluation :
    HEq (coherentColimitApexMiddleFirstValueAfterLast B T)
      (VertexIso.map
        (pointedHomMorphismEvaluationComparison (coherentEdgeHom (SpaceInfinity.δ 2 s)))
        ((ihom (spaceSimplexPointedCoefficients s)).map ug)) :=
  (coherentColimitApexMiddleFirstValueAfterLast_heq_first_post B T).trans
    (coherentColimitApexFirstValueComposite_post_last_heq_evaluation B T)
end
end SerrePositivity.InfinityCategories.F2
