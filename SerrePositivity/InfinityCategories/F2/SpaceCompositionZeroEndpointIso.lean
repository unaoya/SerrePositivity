module

public import SerrePositivity.InfinityCategories.F2.SpaceCompositionZeroEndpointCurry
public import SerrePositivity.InfinityCategories.F2.PointedOppositeTriangleIso

/-!
概要：既存の指定比較の終点同型は元の精密化の反転の同じ全 Hom 作用の類。
方針：既存の射と実終点辺の類の一致、および実辺全体の一致を合成する。
規約：指定同型の値を保持し、単なる同型の存在へ弱めない。
使われ方：元の全族比較の長辺値式の同型としての照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2)))

/-- 既存の指定比較の同じ終点像は元の反転精密化の同じ全 Hom 作用の同型。 -/
lemma spaceCompositionZeroComparison_endpoint_heq_opposite_action :
    HEq (VertexIso.map (spaceCompositionTetrahedronZeroComparison s)
      (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s)))
      (pointedOppositeTriangleActionIso s) := by
  let e := spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)
  let c := VertexIso.map (spaceCompositionTetrahedronZeroComparison s)
    (relativeExtensionFiberEndpoint pointedSpaceProjection b i v
      (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s))
  have he : c.hom = SSet.Truncated.HomotopyCategory.homMk e.toTruncated :=
    spaceCompositionZeroComparison_endpoint_hom s j y (spaceCompositionZeroEndpoint_base s)
  have : IsInvertibleEdge e.toTruncated := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
    rw [← he]
    infer_instance
  have hc : c = asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := by
    apply Iso.ext
    exact he
  have := pointedOppositeTriangleAction_invertible s
  exact (heq_of_eq hc).trans (invertibleEdgeIso_heq_of_edge_eq e
    ((pointedOppositeTriangleCoefficient s).map (pointedOppositeHomAction
      (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)))
      (spaceCompositionZeroEndpointEdge_eq_opposite_action s))

end SerrePositivity.InfinityCategories.F2
