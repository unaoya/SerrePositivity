module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroEndpointIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の指定終点比較と反転精密化の作用の同定を、同じ任意の値写像で保持する。
方針：実辺全体の式から両端の厳密な式を取り出し、既存の像の輸送補題を使う。
規約：HEq から端点を推測せず、元の実辺の両面で証明する。
使われ方：長辺値式に元の指定単位・余単位を代入する前の同じ比較の表示。
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
local notation "Q" => pointedOppositeHomAction K L

/-- 元の指定終点比較の始点は、元の精密化の反転の作用の実始点。 -/
lemma spaceCompositionZeroEndpoint_source_eq_opposite_action :
    (NatTrans.app R (Opposite.op ⦋0⦌)) (spaceSimplexPointedFamilyExtensionVertex M) =
      (NatTrans.app Q (Opposite.op ⦋0⦌))
        (ULift.up (SSet.opObjEquiv.symm (functorVertex
          (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s))))) := by
  let e := spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)
  let f := (pointedOppositeTriangleCoefficient s).map Q
  have h : e.edge = f.edge := spaceCompositionZeroEndpointEdge_eq_opposite_action s
  exact e.src_eq.symm.trans ((congrArg
    (((ihom A).obj (vertexFiber pointedSpaceProjection y)).δ 1) h).trans f.src_eq)

/-- 元の指定終点比較の終点は、元の精密化の反転の作用の実終点。 -/
lemma spaceCompositionZeroEndpoint_target_eq_opposite_action :
    (NatTrans.app R (Opposite.op ⦋0⦌)) (spaceCompositionTetrahedronZeroExtensionVertex s) =
      (NatTrans.app Q (Opposite.op ⦋0⦌))
        (ULift.up (SSet.opObjEquiv.symm
          (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s))))) := by
  let e := spaceCompositionZeroEndpointEdge s j y (spaceCompositionZeroEndpoint_base s)
  let f := (pointedOppositeTriangleCoefficient s).map Q
  have h : e.edge = f.edge := spaceCompositionZeroEndpointEdge_eq_opposite_action s
  exact e.tgt_eq.symm.trans ((congrArg
    (((ihom A).obj (vertexFiber pointedSpaceProjection y)).δ 0) h).trans f.tgt_eq)

/-- 同じ指定比較の値は、任意の同じ値写像で読んでも元の反転精密化の作用の像。 -/
lemma spaceCompositionZeroComparison_endpoint_value_heq_opposite_action
    {Z : SSet.{u + 1}} (V : vertexFiber pointedSpaceProjection y ⟶ Z) :
    HEq (VertexIso.map (VertexIso.map (spaceCompositionTetrahedronZeroComparison s) R)
      ((ihom A).map V))
      (VertexIso.map (pointedOppositeTriangleActionIso s) ((ihom A).map V)) :=
  vertexIso_map_heq_of_heq _ _ (spaceCompositionZeroEndpoint_source_eq_opposite_action s)
    (spaceCompositionZeroEndpoint_target_eq_opposite_action s)
    (spaceCompositionZeroComparison_endpoint_heq_opposite_action s) _

end SerrePositivity.InfinityCategories.F2
