module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceVertexEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportPointPrismNaturality

/-!
概要：全第一辺の三角形族を元の実第一辺で評価し、同じ指定二単体と二実辺を回収する。
方針：元の実頂点での普遍 prism 評価と最後辺普遍輸送の自然性を使う。
規約：元の実第一辺と指定二単体を保持。使われ方：全長辺比較の二成分の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (W : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hp : W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) K ≫
    SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
  (hs : prismEndpoint 0 K ≫ W = f ≫ vertexFiberι pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "q" => coherentColimitRawFirstChoiceVertex B a f W hp hs
local notation "r" => lift (𝟙 K) (SSet.const q)

/-- 全第一辺選択の三角形を、元の実第一辺の同じ実頂点で制限する。 -/
def coherentColimitRawFirstChoiceTriangleAtVertex :
    (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u} :=
  (Δ[2] ◁ r) ≫ coherentColimitRawFirstChoiceTrianglePrism B T f

/-- 元の実第一辺での全三角形の底は、元の同じ指定二単体の全像。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_projection :
    coherentColimitRawFirstChoiceTriangleAtVertex B T f W hp hs ≫ pointedSpaceProjection =
      fst (Δ[2] : SSet.{u + 1}) K ≫ T.diagram ≫ coherentColimitFunctor B := by
  rw [coherentColimitRawFirstChoiceTriangleAtVertex, Category.assoc,
    coherentColimitRawFirstChoiceTrianglePrism_projection, ← Category.assoc, whiskerLeft_fst]

/-- 元の実第一辺での全三角形の第一辺は、同じ元の実 prism そのもの。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      coherentColimitRawFirstChoiceTriangleAtVertex B T f W hp hs = W := by
  rw [coherentColimitRawFirstChoiceTriangleAtVertex, trianglePrism_restrict_baseChange,
    coherentColimitRawFirstChoiceTrianglePrism_first]
  exact coherentColimitRawFirstChoicePrism_at_vertex B a f W hp hs

/-- 元の実第一辺での全三角形の最後辺は、同じ実終点への同じ raw 普遍輸送。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_last
    (g : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)))
    (hg : prismEndpoint 1 K ≫ W = g ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G))) :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫
      coherentColimitRawFirstChoiceTriangleAtVertex B T f W hp hs =
        coherentColimitRawTransportPointPrism B b g := by
  rw [coherentColimitRawFirstChoiceTriangleAtVertex, trianglePrism_restrict_baseChange,
    coherentColimitRawFirstChoiceTrianglePrism_last, coherentColimitRawTransportPointPrism_precomp,
    coherentColimitRawFirstChoiceEndpoint_at_vertex B a f W hp hs g hg]

end SerrePositivity.InfinityCategories.F2
