module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValueCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData

/-!
概要：輸送した元の境界 path の両端は、輸送した二入力の制限に厳密に一致する。
方針：元の値の包含の座標式と、二入力の境界の等式を合成する。
規約：元の境界の path を選び直さない。
使われ方：輸送先の全相対境界図式の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
  {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)

/-- 概要：輸送後の境界 path の始点は第一入力の輸送先の制限。
方針：元の第一値の包含と境界の厳密な式を使う。
規約：元の f。使われ方：相対境界の輸送先の第一端。 -/
lemma relativePathTargetPath_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g
      (d.boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex) =
        A.ι ≫ ((d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) d.vertex) ≫ f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_zero, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g) f, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal_left]
  simp only [← Category.assoc]
  rw [← d.boundary_left]

/-- 概要：輸送後の境界 path の終点は第二入力の輸送先の制限。
方針：元の第二値の包含と境界の厳密な式を使う。
規約：元の g。使われ方：相対境界の輸送先の第二端。 -/
lemma relativePathTargetPath_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g
      (d.boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex) =
        A.ι ≫ ((d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) d.vertex) ≫ g) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_one, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g) g, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal_right]
  simp only [← Category.assoc]
  rw [← d.boundary_right]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
