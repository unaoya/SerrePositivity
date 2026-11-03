module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueMorphismIntervalIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedEdgeTransportValueChange

/-!
概要：元の Space 辺を指定した元の Kan 射で厳密に表示し、同じ全 Hom 成分で値比較する。
方針：実両端と実一次単体の等式だけで、同じ Kan 射の区間比較へ移す。
規約：辺・指定 Kan 射・二成分を保持。使われ方：一つの二単体の三辺の共通の値での比較。
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

/-- 指定 Kan 射の実辺に等しい元の Space 辺の輸送を、同じ元の全 Hom 成分で比較する。 -/
def pointedSpaceMorphismEdgeValueIso {K L : KanObject.{u}} (f : K ⟶ L)
    {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge) :
    FunctorIso (pointedIntervalTransportAt
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ pointedFiberValueTo hy)
      (pointedFiberValueTo hx ≫ (SSet.uliftFunctor.{u + 1, u}).map f) := by
  let u₀ := eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx)
  have hv := (pointedValueMorphismIntervalIso f).precomp u₀
  refine functorIsoOfEq hv
    (pointedIntervalTransportAt_edge_value_change e (pointedRightMorphismEdge f) hx hy he).symm ?_
  rw [← Category.assoc]
  exact congrArg (fun r => r ≫ (SSet.uliftFunctor.{u + 1, u}).map f)
    (pointedFiberValueTo_eq_cast hx).symm

end SerrePositivity.InfinityCategories.F2
