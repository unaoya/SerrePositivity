module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomTriangleValueCoherence

/-!
概要：元の全 Hom の値の比較を、同じ元の Kan 射による評価へ戻す。
方針：指定された長辺・二辺比較へ、同じ右 Hom の値比較の逆を合成する。
規約：元の全係数と比較を保持。使われ方：元の三角形の値の四因子式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))

/-- 元の長辺の全 Hom 比較を、同じ長辺による実値の評価へ戻した比較。 -/
def pointedHomTriangleLongEvaluationComparison :=
  pointedHomTriangleLongValueComparison s ≪≫
    (VertexIso.map (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s))) P).symm

/-- 元の二辺合成の全 Hom 比較を、同じ二辺合成による実値の評価へ戻した比較。 -/
def pointedHomTriangleCompositeEvaluationComparison :=
  pointedHomTriangleCompositeValueComparison s ≪≫
    (VertexIso.map (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
      coherentEdgeHom (SpaceInfinity.δ 0 s))) P).symm

end SerrePositivity.InfinityCategories.F2
