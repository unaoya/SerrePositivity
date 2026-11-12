module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeHomAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite

/-!
概要：元の三角形の精密化を反転し、同じ全 Hom の作用族へ送った指定辺を保持する。
方針：元の辺を edgeOp と宇宙持ち上げで写す。
規約：精密化の代表を選び直さず、両端の反転を明示する。
使われ方：既存の指定比較の終点同型を元の反転精密化の類へ戻す。
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

/-- 元の精密化を反転・持ち上げした指定辺。始点は二辺合成、終点は長辺。 -/
def pointedOppositeTriangleCoefficient :
    ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op).Edge
      (ULift.up (SSet.opObjEquiv.symm (functorVertex
        (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s)))))
      (ULift.up (SSet.opObjEquiv.symm (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s))))) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1}
    (edgeOp (spaceInfinityTriangleEdge s).toTruncated))

/-- 全反転 Hom の作用に送っても元の指定精密化の全一単体を保持する。 -/
lemma pointedOppositeTriangleCoefficient_map_edge :
    ((pointedOppositeTriangleCoefficient s).map (pointedOppositeHomAction K L)).edge =
      (pointedOppositeHomAction K L).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) := rfl

end SerrePositivity.InfinityCategories.F2
