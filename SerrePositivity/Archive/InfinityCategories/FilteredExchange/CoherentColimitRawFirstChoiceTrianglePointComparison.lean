module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceTriangleVertexLongData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceComparisonComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFiberWitnessRestrictedPrism

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

/-- 元の実第一辺で評価した三角形の長辺を、同じ元の長辺普遍 prism と比較する指定値。 -/
def coherentColimitRawFirstChoiceTrianglePointComparison :
    FunctorIso (g ≫ coherentColimitRawFiberTransport B b)
      (f ≫ coherentColimitRawFiberTransport B d) :=
  relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection c (prismEndpoint 0 K)
    (prismEndpoint_zero_leftAnodyne K) v (coherentColimitRawFirstChoice_initial_base B d f)
    (prismEndpoint 1 K) z (coherentColimitRawFirstChoice_final_base B d f)
    ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ X) (coherentColimitRawTransportPointPrism B d f)
    h₀ h₁ s₀ s₁ _ _
    (coherentColimitRawFirstChoiceTriangleAtVertex_long_finish B T f W hp hs g hg)
    (coherentColimitRawTransportPointPrism_finish B d f)

/-- 元の全比較の同じ実頂点の成分は、同じ実長辺と元の普遍 prism の指定比較そのもの。 -/
lemma coherentColimitRawFirstChoiceTriangleComparisonApp_heq_point :
    HEq (coherentColimitRawFirstChoiceTriangleComparisonApp B T f q)
      (coherentColimitRawFirstChoiceTrianglePointComparison B T f W hp hs g hg) := by
  have hh := coherentColimitRawFirstChoiceTriangleComparisonApp_heq_restricted B T f q
  have hr := relativeFiberWitness_heq_restrictedPrism pointedSpaceProjection f
    (intervalMappingUncurry (SSet.const (coherentColimitRawIntervalVertex B d) :
      coherentColimitRawFirstChoiceSpace B a f ⟶ _)) (intervalMappingUncurry_one _) _ _ r
    c v (coherentColimitRawFirstChoice_initial_base B d f)
    (coherentColimitRawFirstChoice_final_base B d f)
    ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ X) (coherentColimitRawTransportPointPrism B d f)
    h₀ h₁ s₀ s₁ (g ≫ coherentColimitRawFiberTransport B b)
    (f ≫ coherentColimitRawFiberTransport B d)
    (coherentColimitRawFirstChoiceTriangleAtVertex_long_finish B T f W hp hs g hg)
    (coherentColimitRawTransportPointPrism_finish B d f)
    (coherentColimitRawFirstChoiceTriangleAtVertex_long_point_prism B T f W hp hs).symm
    (coherentColimitRawConstantEdgeTransport_point_prism B d f q).symm
  exact hh.trans hr.symm

end SerrePositivity.InfinityCategories.F2
