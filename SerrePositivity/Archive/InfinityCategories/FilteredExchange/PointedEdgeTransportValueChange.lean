module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalSourceValueTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportPoint

/-!
概要：同じ実 Space 辺の両端の表示変更を、元の実輸送の値の厳密な等式で保持する。
方針：二つの実頂点等式と辺の厳密な一致だけを消去する。
規約：輸送を選び直さない。使われ方：元の Space 二単体の三辺への値比較の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実辺を指定した二組の端点で読む実輸送は、同じ値射と始域の等式射に整合する。 -/
lemma pointedIntervalTransportAt_edge_value_change
    {x y x' y' : SpaceInfinity.{u} _⦋0⦌} (e : SpaceInfinity.Edge x y)
    (e' : SpaceInfinity.Edge x' y') (hx : x = x') (hy : y = y')
    (he : e.edge = e'.edge) :
    pointedIntervalTransportAt (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ pointedFiberValueTo hy =
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx) ≫
        (pointedIntervalTransportAt (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e'))
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫
          (pointedSpaceFiberValueEquivalence y').hom) := by
  subst x' y'
  have h : e = e' := SSet.Edge.ext he
  subst e'
  simp only [pointedFiberValueTo, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
