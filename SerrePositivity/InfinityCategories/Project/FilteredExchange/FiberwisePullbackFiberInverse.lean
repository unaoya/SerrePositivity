module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：元の値の path 引き戻しの三座標を全空間の fiber へ戻す。
方針：両端条件をそのまま用いて fiber に持ち上げる。
規約：元の path と二入力。使われ方：fiber 比較の逆射。 -/
def fiberwisePullbackFiberInverse :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLift p f g b (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath _ _) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft _ _)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight _ _) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath_zero _ _) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath_one _ _)

/-- 概要：逆射は元の値の全 path を保持。
方針：fiber への持ち上げの path 式。規約：厳密な一致。使われ方：同型の往復。 -/
lemma fiberwisePullbackFiberInverse_path :
    fiberwisePullbackFiberInverse p f g b ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath p f g b =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLift_path _ _ _ _ _ _ _ _ _

/-- 概要：逆射は元の第一値の入力を保持。
方針：fiber への持ち上げの第一脚。規約：厳密な一致。使われ方：同型の第一脚。 -/
lemma fiberwisePullbackFiberInverse_left :
    fiberwisePullbackFiberInverse p f g b ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft p f g b =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLift_left _ _ _ _ _ _ _ _ _

/-- 概要：逆射は元の第二値の入力を保持。
方針：fiber への持ち上げの第二脚。規約：厳密な一致。使われ方：同型の第二脚。 -/
lemma fiberwisePullbackFiberInverse_right :
    fiberwisePullbackFiberInverse p f g b ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight p f g b =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLift_right _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
