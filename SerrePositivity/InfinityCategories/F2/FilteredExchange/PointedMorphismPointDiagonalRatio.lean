module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismEdgeValueRatio
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalPointDiagonalRatio
/-!
概要：元の辺の指定一点対角値の比を、同じ射の作用比較へ接続する。
方針：区間族の比と辺値の比の照合を、一般の実辺の段階で合成する。
規約：元の実辺・両頂点・全初期値と指定値を保持する。
使われ方：Apex の最後辺の raw 比を元の作用比較へ戻す。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
/-- 概要：指定辺値の比への照合を同じ作用比較へ続ける。
方針：一般の実辺で先に合成。規約：元の指定値を保持。使われ方：raw 比の作用表示。 -/
lemma pointedMorphismEdgeValueRatio_heq_action_of_heq {K L : KanObject.{u}}
    (f : K ⟶ L) {C : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge)
    (q : C ⟶ vertexFiber pointedSpaceProjection x) {W : Sort _} (R : W)
    (hR : HEq R ((FunctorIso.precomp (pointedSpaceMorphismEdgeValueIso f e hx hy he) q).symm ≪≫
      ((pointedIntervalTransportAt_universalIso
        (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).precomp q).postcomp (pointedFiberValueTo hy))) :
    HEq R ((pointedValueMorphismUniversalActionIso f).precomp
      (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx))) :=
  hR.trans (pointedMorphismEdgeValueRatio_heq_action f e hx hy he q)
/-- 概要：同じ実辺の指定対角値の比を元の作用比較へ戻す。
方針：元の二つの比の照合を合成。規約：指定値を保持。使われ方：Apex の最後辺。 -/
lemma pointedMorphismPointDiagonalRatio_heq_action_of_heq {K L : KanObject.{u}}
    (f : K ⟶ L) {C : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y)
    (hx : x = spaceInfinityVertex K) (hy : y = spaceInfinityVertex L)
    (he : e.edge = (pointedRightMorphismEdge f).edge)
    (q : C ⟶ vertexFiber pointedSpaceProjection x) {W : Sort _} (R : W)
    (hR : HEq R (pointedIntervalPointDiagonalValueRatio
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) q
      (pointedFiberValueTo hx) (pointedFiberValueTo hy) (SSet.uliftFunctor.map f)
      (pointedSpaceMorphismEdgeValueIso f e hx hy he))) :
    HEq R ((pointedValueMorphismUniversalActionIso f).precomp
      (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hx))) := by
  have h := pointedIntervalPointDiagonal_ratio_heq_factors_of_heq
    (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) q
    (pointedFiberValueTo hx) (pointedFiberValueTo hy) (SSet.uliftFunctor.map f)
    (pointedSpaceMorphismEdgeValueIso f e hx hy he) R hR
  exact pointedMorphismEdgeValueRatio_heq_action_of_heq f e hx hy he q R h
end
end SerrePositivity.InfinityCategories.F2
