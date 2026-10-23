module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanOppositeRefinementIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedOppositeTriangleFunctorIso

/-!
概要：一般の精密化の反転作用を、元の coherent 三角形の指定作用へ戻す。
方針：両実辺の同じ一単体を保ち、同じ類を持つ同型の値の一致を使う。
規約：元の精密化と両端を保持。使われ方：左右輸送の整合の三角形への適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))

/-- 元の反転精密化の作用は、既存の指定三角形作用の同型と値まで一致する。 -/
lemma pointedOppositeRefinementAction_heq_triangle :
    HEq (VertexIso.map (coherentKanOppositeRefinementIso K L (coherentTriangleHomotopy s))
      (pointedOppositeHomAction K L)) (pointedOppositeTriangleActionIso s) := by
  apply vertexIso_heq_of_edge_representatives _ _
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)
      (uliftTruncatedEdge.{u, u + 1} (edgeOp (edgeOfSimplex (coherentTriangleHomotopy s))))).map
        (pointedOppositeHomAction K L))
    ((pointedOppositeTriangleCoefficient s).map (pointedOppositeHomAction K L)) rfl rfl
  change (pointedOppositeHomAction K L).app (Opposite.op ⦋1⦌)
      (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) =
    (pointedOppositeHomAction K L).app (Opposite.op ⦋1⦌)
      (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s)))
  rfl

/-- 同じ類を元の二段作用から長辺作用への関手同型へ正規化する。 -/
lemma pointedOppositeRefinementAction_heq_normalized :
    HEq (VertexIso.map (coherentKanOppositeRefinementIso K L (coherentTriangleHomotopy s))
      (pointedOppositeHomAction K L)) (pointedOppositeTriangleFunctorIso s) :=
  (pointedOppositeRefinementAction_heq_triangle s).trans
    (pointedOppositeTriangleFunctorIso_heq_action s).symm

end SerrePositivity.InfinityCategories.F2
