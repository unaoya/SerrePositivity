module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroEndpointValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeTriangleFunctorIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoWhiskerVertexMap

/-!
概要：既存の指定終点同型の値を、元の二段作用から長辺作用への関手同型へ戻す。
方針：同じ実辺から回収した両端と、反転精密化の作用の厳密な頂点の式を合成する。
規約：元の指定同型と同じ値写像を保持する。
使われ方：元の単位・余単位で長辺値式の三因子を整理する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L
local notation "R" => relativeExtensionFiberEndpoint pointedSpaceProjection b i v
  (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s)

/-- 既存の指定終点同型は同じ元の二段作用から長辺作用への関手同型。 -/
lemma spaceCompositionZeroComparison_endpoint_heq_normalized :
    HEq (VertexIso.map (spaceCompositionTetrahedronZeroComparison s) R)
      (pointedOppositeTriangleFunctorIso s) :=
  (spaceCompositionZeroComparison_endpoint_heq_opposite_action s).trans
    (pointedOppositeTriangleFunctorIso_heq_action s).symm

/-- 元の値写像における指定終点比較の値は同じ正規化した元の関手同型の値。 -/
lemma spaceCompositionZeroComparison_endpoint_value_heq_normalized
    {Z : SSet.{u + 1}} (V : vertexFiber pointedSpaceProjection y ⟶ Z) :
    HEq (VertexIso.map (VertexIso.map (spaceCompositionTetrahedronZeroComparison s) R)
      ((ihom A).map V)) ((pointedOppositeTriangleFunctorIso s).postcomp V) := by
  have hm := vertexIso_map_heq_of_heq
    (VertexIso.map (spaceCompositionTetrahedronZeroComparison s) R)
    (pointedOppositeTriangleFunctorIso s)
    ((spaceCompositionZeroEndpoint_source_eq_opposite_action s).trans
      (pointedOppositeTriangleAction_source_vertex s))
    ((spaceCompositionZeroEndpoint_target_eq_opposite_action s).trans
      (pointedOppositeTriangleAction_target_vertex s))
    (spaceCompositionZeroComparison_endpoint_heq_normalized s) ((ihom A).map V)
  exact hm.trans (functorIso_postcomp_vertexMap_heq (pointedOppositeTriangleFunctorIso s) V).symm

end SerrePositivity.InfinityCategories.F2
