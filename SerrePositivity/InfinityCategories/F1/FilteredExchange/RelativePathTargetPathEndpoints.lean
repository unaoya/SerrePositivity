module

public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackValueCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathInputTransportData

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
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)

/-- 概要：輸送後の境界 path の始点は第一入力の輸送先の制限。
方針：元の第一値の包含と境界の厳密な式を使う。
規約：元の f。使われ方：相対境界の輸送先の第一端。 -/
lemma relativePathTargetPath_zero :
    prismEndpoint 0 (A : SSet.{u}) ≫ fiberwisePullbackPathPrism p f g
      (d.boundaryValue ≫ fiberwisePullbackValueToTotal p f g d.vertex) =
        A.ι ≫ ((d.leftValue ≫ vertexFiberι (f ≫ p) d.vertex) ≫ f) := by
  rw [fiberwisePullbackPathPrism_zero, Category.assoc,
    ← Category.assoc (fiberwisePullbackValueToTotal p f g d.vertex)
      (fiberwiseIntervalPullbackLeft p f g) f, fiberwisePullbackValueToTotal_left]
  simp only [← Category.assoc]
  rw [← d.boundary_left]

/-- 概要：輸送後の境界 path の終点は第二入力の輸送先の制限。
方針：元の第二値の包含と境界の厳密な式を使う。
規約：元の g。使われ方：相対境界の輸送先の第二端。 -/
lemma relativePathTargetPath_one :
    prismEndpoint 1 (A : SSet.{u}) ≫ fiberwisePullbackPathPrism p f g
      (d.boundaryValue ≫ fiberwisePullbackValueToTotal p f g d.vertex) =
        A.ι ≫ ((d.rightValue ≫ vertexFiberι (g ≫ p) d.vertex) ≫ g) := by
  rw [fiberwisePullbackPathPrism_one, Category.assoc,
    ← Category.assoc (fiberwisePullbackValueToTotal p f g d.vertex)
      (fiberwiseIntervalPullbackRight p f g) g, fiberwisePullbackValueToTotal_right]
  simp only [← Category.assoc]
  rw [← d.boundary_right]

end SerrePositivity.InfinityCategories.F2
