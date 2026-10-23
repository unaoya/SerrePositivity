module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstChoiceTrianglePointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawTriangleLongPointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleFixedEdgesUniversalFiberComparison

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

/-- 元の実第一辺で評価した指定長辺比較は、同じ二実辺を持つ元の全持ち上げの比較に等しい。 -/
lemma coherentColimitRawFirstChoiceTrianglePointComparison_eq_of_fixed_edges :
    coherentColimitRawFirstChoiceTrianglePointComparison B T f W hp hs g hg =
      coherentColimitRawTriangleLongPointComparison B T f W hs g Y hY hfirst hlast := by
  exact triangleFixedEdgesUniversalFiberComparison_eq pointedSpaceProjection
    (fst (Δ[2] : SSet.{u + 1}) K ≫ T.diagram ≫ coherentColimitFunctor B) W
    (hp.trans (coherentColimitRawTriangle_face B a T.diagram 2 T.face_two).symm) z
    (coherentColimitRawTriangle_terminal_base B T f) X Y
    (coherentColimitRawFirstChoiceTriangleAtVertex_projection B T f W hp hs) hY
    (coherentColimitRawFirstChoiceTriangleAtVertex_first B T f W hp hs) hfirst
    (g ≫ coherentColimitRawFiberTransport B b)
    (by simpa only [Category.assoc] using
      coherentColimitRawFirstChoiceTriangleAtVertex_long_finish B T f W hp hs g hg)
    (by simpa only [Category.assoc] using coherentColimitRawTriangleLong_finish B g Y hlast)
    ((coherentColimitRawFirstChoiceTriangleAtVertex_last B T f W hp hs g hg).trans hlast.symm)
    c (coherentColimitRawTriangle_face B d T.diagram 1 T.face_one).symm
    v hs.symm (coherentColimitRawFirstChoice_initial_base B d f)
    (coherentColimitRawFirstChoice_final_base B d f) h₀
    (coherentColimitRawTriangleLong_projection B T Y hY) s₀
    (coherentColimitRawTriangleLong_start B f W hs Y hfirst)
    (coherentColimitRawTransportPointPrism B d f)
    (coherentColimitRawTransportPointPrism_projection B d f)
    (coherentColimitRawTransportPointPrism_start B d f)
    (f ≫ coherentColimitRawFiberTransport B d) (coherentColimitRawTransportPointPrism_finish B d f)

end SerrePositivity.InfinityCategories.F2
