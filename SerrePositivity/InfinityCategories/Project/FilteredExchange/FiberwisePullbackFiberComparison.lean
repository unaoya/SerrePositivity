module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackLift

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：fiber の三座標を元の値の path 引き戻しへまとめる。
方針：元の二つの fiber 射に対する両端式を使う。
規約：全 path を保持。使われ方：fiber 同型の順方向。 -/
def fiberwisePullbackFiberComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b ⟶
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift _ _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath p f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft p f g b) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight p f g b)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath_zero p f g b) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath_one p f g b)

/-- 概要：比較は元の fiber 内の path を保持する。
方針：持ち上げの第一座標。規約：全 path。使われ方：fiber 同型の往復。 -/
lemma fiberwisePullbackFiberComparison_path :
    fiberwisePullbackFiberComparison p f g b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath p f g b :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_path _ _ _ _ _ _ _

/-- 概要：比較は元の第一 fiber 入力を保持する。
方針：持ち上げの第二座標。規約：元の第一値。使われ方：fiber 同型の第一脚。 -/
lemma fiberwisePullbackFiberComparison_left :
    fiberwisePullbackFiberComparison p f g b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft p f g b :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_left _ _ _ _ _ _ _

/-- 概要：比較は元の第二 fiber 入力を保持する。
方針：持ち上げの第三座標。規約：元の第二値。使われ方：fiber 同型の第二脚。 -/
lemma fiberwisePullbackFiberComparison_right :
    fiberwisePullbackFiberComparison p f g b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight p f g b :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_right _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
