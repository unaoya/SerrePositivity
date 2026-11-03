module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorFiber
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePathFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram

/-!
概要：path 引き戻しの fiber の三座標は、元の値の cospan の両端条件を満たす。
方針：元の fiber の単射な包含後に全空間の指定両端条件を比較する。
規約：元の f・g が誘導する fiber 射を使う。
使われ方：fiber から元の値の path 引き戻しへの厳密な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：fiber の path の指定端点を含めると元の全空間の指定端点。
方針：path の fiber 同型と誘導射の包含式を合成する。
規約：二端点を同時に扱う。使われ方：元の fiber 内の両端条件の検査。 -/
lemma fiberwisePullbackFiberPath_endpoint_ι (e : Fin 2) :
    fiberwisePullbackFiberPath p f g b ≫
      (intervalEndpointNatTrans e).app (vertexFiber p b) ≫ vertexFiberι p b =
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
        fiberwiseIntervalPullbackPath p f g ≫ fiberwiseIntervalEndpoint p e := by
  rw [fiberwisePullbackFiberPath, Category.assoc,
    fiberwiseFunctorFiberIso_interval_endpoint, ← Category.assoc, vertexFiberMap_ι, Category.assoc]

/-- 概要：fiber 内の始点は元の第一 fiber 射の像。
方針：標的 fiber の包含後に元の path の始点式を使う。
規約：元の第一射 f。使われ方：値の path 引き戻しへの第一段の持ち上げ。 -/
lemma fiberwisePullbackFiberPath_zero :
    fiberwisePullbackFiberPath p f g b ≫ (intervalEndpointNatTrans 0).app (vertexFiber p b) =
      fiberwisePullbackFiberLeft p f g b ≫ vertexFiberMap (f ≫ p) p f rfl b := by
  apply (cancel_mono (vertexFiberι p b)).1
  rw [Category.assoc, fiberwisePullbackFiberPath_endpoint_ι,
    fiberwiseIntervalPullbackPath_zero, ← Category.assoc, ← fiberwisePullbackFiberLeft_ι]
  rw [Category.assoc, Category.assoc, vertexFiberMap_ι]

/-- 概要：fiber 内の終点は元の第二 fiber 射の像。
方針：標的 fiber の包含後に元の path の終点式を使う。
規約：元の第二射 g。使われ方：値の path 引き戻しへの第二段の持ち上げ。 -/
lemma fiberwisePullbackFiberPath_one :
    fiberwisePullbackFiberPath p f g b ≫ (intervalEndpointNatTrans 1).app (vertexFiber p b) =
      fiberwisePullbackFiberRight p f g b ≫ vertexFiberMap (g ≫ p) p g rfl b := by
  apply (cancel_mono (vertexFiberι p b)).1
  rw [Category.assoc, fiberwisePullbackFiberPath_endpoint_ι,
    fiberwiseIntervalPullbackPath_one, ← Category.assoc, ← fiberwisePullbackFiberRight_ι]
  rw [Category.assoc, Category.assoc, vertexFiberMap_ι]

end SerrePositivity.InfinityCategories.F2
