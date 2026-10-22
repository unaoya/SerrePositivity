module

public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportPointPrism
public import SerrePositivity.InfinityCategories.F2.CoherentColimitPointValueToFiberTransport

/-!
概要：元の余極限指定辺に沿う raw fiber 輸送と、その同じ実 pointed prism を保持する。
方針：同じ区間族の同じ零単体を使い、元の辺の実一次単体を底として回収する。
規約：辺・指定点・全初期値を保持。使われ方：元の定値三角形の最後辺の普遍輸送化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (b : SSet.Homotopy G J)
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 元の余錐両頂点の間の、同じ指定辺と同じ指定点の実 fiber 輸送。 -/
def coherentColimitRawFiberTransport := pointedIntervalTransportAt A l

variable {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)))

/-- 元の全初期値から元の指定辺に沿う、同じ普遍輸送の実 pointed prism。 -/
def coherentColimitRawTransportPointPrism := pointedIntervalTransportPointPrism A l f

/-- 元の実 prism の始点は元の初期値の同じ pointed 包含。 -/
lemma coherentColimitRawTransportPointPrism_start :
    prismEndpoint 0 K ≫ coherentColimitRawTransportPointPrism B b f =
      f ≫ vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)) :=
  pointedIntervalTransportPointPrism_start A l f

/-- 元の実 prism の終点は同じ raw fiber 輸送の同じ全初期値による前合成。 -/
lemma coherentColimitRawTransportPointPrism_finish :
    prismEndpoint 1 K ≫ coherentColimitRawTransportPointPrism B b f =
      (f ≫ coherentColimitRawFiberTransport B b) ≫
        vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone J)) :=
  pointedIntervalTransportPointPrism_finish A l f

/-- 元の実 prism の底は、元の指定余極限辺の同じ一次単体を全係数で引き戻したもの。 -/
lemma coherentColimitRawTransportPointPrism_projection :
    coherentColimitRawTransportPointPrism B b f ≫ pointedSpaceProjection =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B b).edge := by
  rw [coherentColimitRawTransportPointPrism, pointedIntervalTransportPointPrism_projection,
    coherentColimitRawIntervalVertex_uncurry, ← Category.assoc, whiskerLeft_fst]

omit f in
/-- 同じ raw 輸送の固定値への像は、同じ native 輸送の元の値への像そのもの。 -/
lemma coherentColimitRawFiberTransport_valueTo :
    coherentColimitRawFiberTransport B b ≫
      pointedFiberValueTo (coherentDiagramTotalCocone_vertex J) =
    coherentColimitFiberTransport B b ≫
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J)).hom :=
  pointedIntervalTransportAt_valueTo_eq (coherentDiagramTotalCocone_vertex J) A _
    (coherentColimitRawIntervalFamily_heq_native B b) l

end SerrePositivity.InfinityCategories.F2
