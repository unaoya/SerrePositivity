module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstChoicePointIndependence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawTrianglePointTransport

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

local notation "X" => coherentColimitRawFirstChoiceTriangleAtVertex B T f W hp hs

local notation "c" => fst Δ[1] K ≫ SSet.yonedaEquiv.symm
  (SSet.Truncated.Edge.edge (coherentColimitFunctorEdge B d))
local notation "v" => f ≫ vertexFiberι pointedSpaceProjection
  (JoinCocone.vertex (coherentDiagramTotalCocone F))
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "h₀" => coherentColimitRawFirstChoiceTriangleAtVertex_long_projection B T f W hp hs
local notation "h₁" => coherentColimitRawTransportPointPrism_projection B d f
local notation "s₀" => coherentColimitRawFirstChoiceTriangleAtVertex_long_start B T f W hp hs
local notation "s₁" => coherentColimitRawTransportPointPrism_start B d f
variable (g : K ⟶ vertexFiber pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone G)))
  (hg : prismEndpoint 1 K ≫ W = g ≫ vertexFiberι pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone G)))

variable (Y : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hY : Y ≫ pointedSpaceProjection = fst (Δ[2] : SSet.{u + 1}) K ≫
    T.diagram ≫ coherentColimitFunctor B)
  (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ Y = W)
  (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ Y = coherentColimitRawTransportPointPrism B b g)

variable
  (U : FiberTransportFamily (b := JoinCocone.vertex (coherentDiagramTotalCocone J))
    pointedSpaceProjection f (intervalMappingUncurry
      (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d))))
  (hU : (Δ[1] ◁ lift (𝟙 K) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ U.prism =
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Y)

include hY hfirst hlast hg hU in
/-- 同じ実二辺を持つ元の全長辺輸送の一点値は、全比較の同じ実第一辺成分に厳密に一致。 -/
lemma coherentColimitRawFirstChoiceTriangleComparisonApp_heq_transport :
    HEq (coherentColimitRawFirstChoiceTriangleComparisonApp B T f q)
      ((pointedIntervalTransportComparison f
        (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)) U).precomp
          (lift (𝟙 K) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))))) := by
  exact (coherentColimitRawFirstChoiceTriangleComparisonApp_heq_point B T f W hp hs g hg).trans
    ((heq_of_eq (coherentColimitRawFirstChoiceTrianglePointComparison_eq_of_fixed_edges
      B T f W hp hs g hg Y hY hfirst hlast)).trans
      (coherentColimitRawTriangleLongPointComparison_heq_transport
        B T f W hs g Y hY hfirst hlast U hU))

end SerrePositivity.InfinityCategories.F2
