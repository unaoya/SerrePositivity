module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValueCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTransportTarget

/-!
概要：輸送先の相対境界の元の標的値内の三座標を厳密に照合する。
方針：元の fiber の単射な包含後で、境界の二端点と全 path の式を使う。
規約：元の境界の値と二入力の値を変更しない。
使われ方：輸送した有限模型の指定境界を元の値で読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
  {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)

/-- 概要：輸送先の相対境界の始点は元の第一値の像。
方針：標的 fiber の包含後に区間境界の始点を評価する。
規約：元の fiber 射。使われ方：有限模型の始点の厳密な照合。 -/
lemma relativePathTransportTargetFiber_zero :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d =
      d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl d.vertex := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p d.vertex
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_ends, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

/-- 概要：輸送先の相対境界の終点は元の第二値の像。
方針：標的 fiber の包含後に区間境界の終点を評価する。
規約：元の fiber 射。使われ方：有限模型の終点の厳密な照合。 -/
lemma relativePathTransportTargetFiber_one :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d =
      d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl d.vertex := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p d.vertex
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_ends, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

/-- 概要：輸送先の相対境界の全部分 path は、元の境界値の元の全 path そのもの。
方針：単射な包含後に元の値の全 path の比較式を uncurry する。
規約：高次単体も保持。使われ方：元の値での指定境界の厳密な反映。 -/
lemma relativePathTransportTargetFiber_side :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d =
      uncurry (d.boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl d.vertex)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl d.vertex)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p d.vertex
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTarget_side]
  have h := congrArg (fun r ↦ uncurry (d.boundaryValue ≫ r))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal_path p f g d.vertex)
  rw [← Category.assoc d.boundaryValue _
    ((ihom (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex)), uncurry_natural_right] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism, Category.assoc] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
