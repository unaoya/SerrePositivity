module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalPrismVertex

/-!
概要：元の全第一辺の評価を元の実頂点へ戻すと、同じ実 prism・実 fiber 終点を回収する。
方針：同じ実頂点を定める相対延長の全評価の式を使う。
規約：元の実 prism と実終点を保持。使われ方：全長辺比較の二成分の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
  {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (W : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hp : W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) K ≫
    SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
  (hs : prismEndpoint 0 K ≫ W = f ≫ vertexFiberι pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "q" => coherentColimitRawFirstChoiceVertex B a f W hp hs
local notation "t" => lift (𝟙 K) (SSet.const q)

/-- 全第一辺の同じ実頂点での普遍評価は、元の実 prism そのもの。 -/
lemma coherentColimitRawFirstChoicePrism_at_vertex :
    (Δ[1] ◁ t) ≫ coherentColimitRawFirstChoicePrism B a f = W :=
  relativeExtensionUniversalPrism_at_vertex _ _ _ _ W hp hs

/-- 全第一辺の同じ実頂点での fiber 終点は、元の実終点射そのもの。 -/
lemma coherentColimitRawFirstChoiceEndpoint_at_vertex
    (g : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)))
    (hg : prismEndpoint 1 K ≫ W = g ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G))) :
    t ≫ coherentColimitRawFirstChoiceEndpoint B a f = g :=
  relativeExtensionUniversalPrismEndpoint_at_vertex _ _ _ _ W hp hs _ _ g hg

/-- 元の同じ実第一辺の全 fiber 終点の curry の値は、元の同じ実終点射の関手頂点。 -/
lemma coherentColimitRawFirstChoiceEndpoint_vertex
    (g : K ⟶ vertexFiber pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)))
    (hg : prismEndpoint 1 K ≫ W = g ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G))) :
    (curry (coherentColimitRawFirstChoiceEndpoint B a f)).app (Opposite.op ⦋0⦌) q =
      functorVertex g := by
  rw [coherentColimitRawFirstChoiceEndpoint, relativeExtensionUniversalPrismEndpoint,
    curry_uncurry]
  exact relativeExtensionFiberEndpoint_vertex _ _ _ _ _ _ _ _ W hp hs g hg

end SerrePositivity.InfinityCategories.F2
