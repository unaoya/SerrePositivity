module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberLift
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates

/-!
概要：元の値の path 引き戻しから全空間の同じ底の fiber への逆射。
方針：元の三座標と両端条件を保った fiber への持ち上げを使う。
規約：元の f・g の fiber 射を用いる。
使われ方：path 引き戻しの fiber 同型の逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：元の値の path 引き戻しの三座標を全空間の fiber へ戻す。
方針：両端条件をそのまま用いて fiber に持ち上げる。
規約：元の path と二入力。使われ方：fiber 比較の逆射。 -/
def fiberwisePullbackFiberInverse :
    intervalPullback (vertexFiberMap (f ≫ p) p f rfl b) (vertexFiberMap (g ≫ p) p g rfl b) ⟶
      vertexFiber (fiberwiseIntervalPullbackProjection p f g) b :=
  fiberwisePullbackFiberLift p f g b (intervalPullbackPath _ _) (intervalPullbackLeft _ _)
    (intervalPullbackRight _ _) (intervalPullbackPath_zero _ _) (intervalPullbackPath_one _ _)

/-- 概要：逆射は元の値の全 path を保持。
方針：fiber への持ち上げの path 式。規約：厳密な一致。使われ方：同型の往復。 -/
lemma fiberwisePullbackFiberInverse_path :
    fiberwisePullbackFiberInverse p f g b ≫ fiberwisePullbackFiberPath p f g b =
      intervalPullbackPath (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) := fiberwisePullbackFiberLift_path _ _ _ _ _ _ _ _ _

/-- 概要：逆射は元の第一値の入力を保持。
方針：fiber への持ち上げの第一脚。規約：厳密な一致。使われ方：同型の第一脚。 -/
lemma fiberwisePullbackFiberInverse_left :
    fiberwisePullbackFiberInverse p f g b ≫ fiberwisePullbackFiberLeft p f g b =
      intervalPullbackLeft (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) := fiberwisePullbackFiberLift_left _ _ _ _ _ _ _ _ _

/-- 概要：逆射は元の第二値の入力を保持。
方針：fiber への持ち上げの第二脚。規約：厳密な一致。使われ方：同型の第二脚。 -/
lemma fiberwisePullbackFiberInverse_right :
    fiberwisePullbackFiberInverse p f g b ≫ fiberwisePullbackFiberRight p f g b =
      intervalPullbackRight (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) := fiberwisePullbackFiberLift_right _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
