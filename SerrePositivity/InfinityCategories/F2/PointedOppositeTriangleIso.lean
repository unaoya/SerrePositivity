module

public import SerrePositivity.InfinityCategories.F2.PointedOppositeTriangleCoefficient
public import SerrePositivity.InfinityCategories.F2.InvertibleEdgeIsoEquality

/-!
概要：元の精密化の反転の作用を、その同じ辺の類の同型として保持する。
方針：元の Kan Hom の可逆辺を反転・持ち上げ・作用族で写す。
規約：別の path を選ばず同じ実一単体の類を使う。
使われ方：元の指定比較の終点同型の Hom 作用表示。
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

/-- 元の精密化の反転の全 Hom 作用の辺は、同じ元の逆三角形を写した可逆辺。 -/
lemma pointedOppositeTriangleAction_invertible :
    IsInvertibleEdge (((pointedOppositeTriangleCoefficient s).map
      (pointedOppositeHomAction K L)).toTruncated) := by
  have h : IsInvertibleEdge (spaceInfinityTriangleEdge s).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact (h.op.ulift.{u, u + 1}).map (pointedOppositeHomAction K L)

/-- 元の指定精密化の反転の全 Hom 作用の、同じ実辺の類の同型。 -/
def pointedOppositeTriangleActionIso :
    VertexIso
      ((pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (functorVertex
          (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s))))))
      ((pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm
          (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))))) := by
  have := pointedOppositeTriangleAction_invertible s
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (((pointedOppositeTriangleCoefficient s).map (pointedOppositeHomAction K L)).toTruncated))

end SerrePositivity.InfinityCategories.F2
