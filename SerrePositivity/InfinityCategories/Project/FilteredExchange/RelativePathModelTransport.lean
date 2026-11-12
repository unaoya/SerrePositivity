module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeLeftFibrationTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundaryTransportProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTransportTarget

/-!
概要：元の全相対境界の輸送を厳密に保ち、標的の有限模型本体を元の同じ値へ輸送する。
方針：貼り合わせた全境界円柱を、単射な境界に沿う相対 fiber 持ち上げへ指定する。
規約：境界終点・境界全円柱・模型の底の全円柱を同時に保持する。
使われ方：一般 coherent filtered 引き戻し比較の境界付き相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：境界 path と二入力の指定全円柱を保つ、標的模型本体の元の値への輸送。
方針：元の全境界ホモトピーを相対 left fibration 持ち上げに渡す。
規約：新たな境界輸送を仮定しない。使われ方：相対有限 path 模型の同時輸送の最終段。 -/
lemma relativePath_model_transport {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M) [Mono m] (q : M ⟶ H)
    (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    ∃ w : M ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex, m ≫ w = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d ∧
      ∃ G : SSet.Homotopy q (w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex),
        (m ▷ (Δ[1] : SSet.{u})) ≫ G.h = (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ∧
        G.h ≫ p = d.modelBase.h := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he
  let L' : SSet.Homotopy (m ≫ q)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex) :=
    { h := L.h
      h₀ := L.h₀
      h₁ := by
        change SSet.ι₁ ≫ L.h = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex
        rw [L.h₁, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber_ι]
      rel := L.rel }
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.leftFibration_transport_to_fiber_relative p m q d.vertex d.modelBase
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d) L'
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy_projection d hk he)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
