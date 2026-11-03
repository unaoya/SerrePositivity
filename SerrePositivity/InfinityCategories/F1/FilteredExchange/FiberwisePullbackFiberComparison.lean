module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberEndpoints
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackLift

/-!
概要：path 引き戻しの fiber から、元の三つの値の path 引き戻しへの比較。
方針：fiber 内の三座標と厳密な両端条件から持ち上げる。
規約：元の f・g の fiber 射を使う。
使われ方：全空間の fiber が元の値の ∞ 引き戻しを表すことの確認。
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

/-- 概要：fiber の三座標を元の値の path 引き戻しへまとめる。
方針：元の二つの fiber 射に対する両端式を使う。
規約：全 path を保持。使われ方：fiber 同型の順方向。 -/
def fiberwisePullbackFiberComparison : vertexFiber (fiberwiseIntervalPullbackProjection p f g) b ⟶
    intervalPullback (vertexFiberMap (f ≫ p) p f rfl b) (vertexFiberMap (g ≫ p) p g rfl b) :=
  intervalPullbackLift _ _ (fiberwisePullbackFiberPath p f g b)
    (fiberwisePullbackFiberLeft p f g b) (fiberwisePullbackFiberRight p f g b)
    (fiberwisePullbackFiberPath_zero p f g b) (fiberwisePullbackFiberPath_one p f g b)

/-- 概要：比較は元の fiber 内の path を保持する。
方針：持ち上げの第一座標。規約：全 path。使われ方：fiber 同型の往復。 -/
lemma fiberwisePullbackFiberComparison_path :
    fiberwisePullbackFiberComparison p f g b ≫
      intervalPullbackPath (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) = fiberwisePullbackFiberPath p f g b :=
  intervalPullbackLift_path _ _ _ _ _ _ _

/-- 概要：比較は元の第一 fiber 入力を保持する。
方針：持ち上げの第二座標。規約：元の第一値。使われ方：fiber 同型の第一脚。 -/
lemma fiberwisePullbackFiberComparison_left :
    fiberwisePullbackFiberComparison p f g b ≫
      intervalPullbackLeft (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) = fiberwisePullbackFiberLeft p f g b :=
  intervalPullbackLift_left _ _ _ _ _ _ _

/-- 概要：比較は元の第二 fiber 入力を保持する。
方針：持ち上げの第三座標。規約：元の第二値。使われ方：fiber 同型の第二脚。 -/
lemma fiberwisePullbackFiberComparison_right :
    fiberwisePullbackFiberComparison p f g b ≫
      intervalPullbackRight (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) = fiberwisePullbackFiberRight p f g b :=
  intervalPullbackLift_right _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
