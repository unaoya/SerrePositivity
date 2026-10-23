module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueMorphismIntervalIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceEdgeCanonicalVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedEdgeTransportValueChange

/-!
概要：元の任意の Space 辺の実区間輸送を、その同じ辺の元の Kan 射へ値比較する。
方針：辺の厳密な復元と実両端の等式で、元の全 Hom 比較の同じ成分へ戻す。
規約：辺・元の射・二つの指定成分を保持。使われ方：元の余極限二単体の三辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 任意の元の Space 辺の実輸送は、同じ元の辺の Kan 射と同じ全 Hom 指定値で整合。 -/
def pointedSpaceEdgeValueIso {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y) :
    FunctorIso (pointedIntervalTransportAt
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫
        pointedFiberValueTo (spaceEdge_target_to_object e))
      (pointedFiberValueTo (spaceEdge_source_to_object e) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom e.edge)) := by
  let f := coherentEdgeHom e.edge
  let u₀ := eqToHom (congrArg (vertexFiber pointedSpaceProjection) (spaceEdge_source_to_object e))
  have he := (pointedValueMorphismIntervalIso f).precomp u₀
  refine functorIsoOfEq he
    (pointedIntervalTransportAt_edge_value_change e (pointedRightMorphismEdge f)
      (spaceEdge_source_to_object e) (spaceEdge_target_to_object e)
      (pointedRightMorphismEdge_recover e.edge).symm).symm ?_
  rw [← Category.assoc]
  exact congrArg (fun r => r ≫ (SSet.uliftFunctor.{u + 1, u}).map f)
    (pointedFiberValueTo_eq_cast (spaceEdge_source_to_object e)).symm

end SerrePositivity.InfinityCategories.F2
