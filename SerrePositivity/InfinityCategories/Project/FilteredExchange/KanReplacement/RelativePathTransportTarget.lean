module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTargetPathEndpoints

/-!
概要：輸送先の元の境界 path と二入力を貼り合わせた、全相対境界の図式。
方針：両端の一致を使い、元の相対境界の押し出しで貼る。
規約：元の同じ頂点の値の境界 path を使用する。
使われ方：標的有限模型の相対輸送の指定終点。
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

/-- 概要：輸送した境界 path と二入力の像を全相対境界上で貼る。
方針：指定された三座標の相対境界図式を作る。
規約：元の境界と入力の輸送先。使われ方：有限模型の終点境界。 -/
def relativePathTransportTarget : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ H :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram A ((d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) d.vertex) ≫ f)
    ((d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) d.vertex) ≫ g)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g
      (d.boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTargetPath_zero d) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTargetPath_one d)

/-- 概要：輸送先の相対境界図式の部分 path は元の値の境界 path の像。
方針：押し出しの第一脚。規約：全 path を保持。使われ方：元の境界輸送の全円柱の指定。 -/
lemma relativePathTransportTarget_side :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ relativePathTransportTarget d =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g
        (d.boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g d.vertex) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram_side A _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTargetPath_zero d)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTargetPath_one d)

/-- 概要：輸送先の相対境界図式の二端点は元の二入力の輸送先。
方針：押し出しの第二脚。規約：全二端点。使われ方：二入力の全円柱の指定。 -/
lemma relativePathTransportTarget_ends :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ relativePathTransportTarget d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram ((d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) d.vertex) ≫ f)
        ((d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) d.vertex) ≫ g) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram_ends A _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTargetPath_zero d)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTargetPath_one d)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
