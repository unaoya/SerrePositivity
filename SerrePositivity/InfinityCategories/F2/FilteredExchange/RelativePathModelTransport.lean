module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathBoundaryTransportProjection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeLeftFibrationTransport

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：境界 path と二入力の指定全円柱を保つ、標的模型本体の元の値への輸送。
方針：元の全境界ホモトピーを相対 left fibration 持ち上げに渡す。
規約：新たな境界輸送を仮定しない。使われ方：相対有限 path 模型の同時輸送の最終段。 -/
lemma relativePath_model_transport {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (m : relativePathBoundaryShape A ⟶ M) [Mono m] (q : M ⟶ H)
    (d : RelativePathInputTransportData p f g A u v a m q)
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    ∃ w : M ⟶ vertexFiber p d.vertex, m ≫ w = relativePathTransportTargetFiber d ∧
      ∃ G : SSet.Homotopy q (w ≫ vertexFiberι p d.vertex),
        (m ▷ (Δ[1] : SSet.{u})) ≫ G.h = (relativePathBoundaryTransportHomotopy d hk he).h ∧
        G.h ≫ p = d.modelBase.h := by
  let L := relativePathBoundaryTransportHomotopy d hk he
  let L' : SSet.Homotopy (m ≫ q)
      (relativePathTransportTargetFiber d ≫ vertexFiberι p d.vertex) :=
    { h := L.h
      h₀ := L.h₀
      h₁ := by
        change SSet.ι₁ ≫ L.h = relativePathTransportTargetFiber d ≫ vertexFiberι p d.vertex
        rw [L.h₁, relativePathTransportTargetFiber_ι]
      rel := L.rel }
  exact leftFibration_transport_to_fiber_relative p m q d.vertex d.modelBase
    (relativePathTransportTargetFiber d) L'
    (relativePathBoundaryTransportHomotopy_projection d hk he)

end SerrePositivity.InfinityCategories.F2
