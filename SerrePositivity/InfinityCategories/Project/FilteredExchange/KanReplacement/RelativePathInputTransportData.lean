module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary

/-!
概要：有限模型の底・元の境界・二入力の全輸送を一つの指定データとして記録する。
方針：同じ頂点の値と全円柱、境界・底の全時刻の厳密な式を保持する。
規約：存在や充填性を仮定する構造ではなく、実際に構成するデータ。
使われ方：有限模型の全相対境界輸送を貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の境界と二入力を保つ、有限 path 模型の指定底輸送の全データ。
方針：元の各円柱と厳密な境界式を記録する。
規約：構成済みの元の値を使用。使われ方：標的有限模型の相対持ち上げの入力。 -/
structure RelativePathInputTransportData {K M E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M) (q : M ⟶ H) where
  vertex : B _⦋0⦌
  boundaryValue : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl vertex)
  modelBase : SSet.Homotopy (q ≫ p) (SSet.const vertex)
  boundaryHomotopy : SSet.Homotopy a
    (boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g vertex)
  leftValue : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (f ≫ p) vertex
  rightValue : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (g ≫ p) vertex
  leftHomotopy : SSet.Homotopy u (leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) vertex)
  rightHomotopy : SSet.Homotopy v (rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) vertex)
  boundary_left : A.ι ≫ leftValue = boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl vertex)
  boundary_right : A.ι ≫ rightValue = boundaryValue ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl vertex)
  left_restrict : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ leftHomotopy.h =
    boundaryHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g
  right_restrict : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ rightHomotopy.h =
    boundaryHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g
  left_projection : leftHomotopy.h ≫ (f ≫ p) =
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 0 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ modelBase.h
  right_projection : rightHomotopy.h ≫ (g ≫ p) =
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEndpoint A 1 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ modelBase.h
  path_projection : ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ modelBase.h =
    (snd (Δ[1] : SSet.{u}) (A : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      boundaryHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g

end SerrePositivity.InfinityCategories.Project.FilteredExchange
