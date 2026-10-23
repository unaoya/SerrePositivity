module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackValueCoordinates

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の境界と二入力を保つ、有限 path 模型の指定底輸送の全データ。
方針：元の各円柱と厳密な境界式を記録する。
規約：構成済みの元の値を使用。使われ方：標的有限模型の相対持ち上げの入力。 -/
structure RelativePathInputTransportData {K M E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (m : relativePathBoundaryShape A ⟶ M) (q : M ⟶ H) where
  vertex : B _⦋0⦌
  boundaryValue : (A : SSet.{u}) ⟶ intervalPullback
    (vertexFiberMap (f ≫ p) p f rfl vertex) (vertexFiberMap (g ≫ p) p g rfl vertex)
  modelBase : SSet.Homotopy (q ≫ p) (SSet.const vertex)
  boundaryHomotopy : SSet.Homotopy a
    (boundaryValue ≫ fiberwisePullbackValueToTotal p f g vertex)
  leftValue : K ⟶ vertexFiber (f ≫ p) vertex
  rightValue : K ⟶ vertexFiber (g ≫ p) vertex
  leftHomotopy : SSet.Homotopy u (leftValue ≫ vertexFiberι (f ≫ p) vertex)
  rightHomotopy : SSet.Homotopy v (rightValue ≫ vertexFiberι (g ≫ p) vertex)
  boundary_left : A.ι ≫ leftValue = boundaryValue ≫ intervalPullbackLeft
    (vertexFiberMap (f ≫ p) p f rfl vertex) (vertexFiberMap (g ≫ p) p g rfl vertex)
  boundary_right : A.ι ≫ rightValue = boundaryValue ≫ intervalPullbackRight
    (vertexFiberMap (f ≫ p) p f rfl vertex) (vertexFiberMap (g ≫ p) p g rfl vertex)
  left_restrict : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ leftHomotopy.h =
    boundaryHomotopy.h ≫ fiberwiseIntervalPullbackLeft p f g
  right_restrict : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ rightHomotopy.h =
    boundaryHomotopy.h ≫ fiberwiseIntervalPullbackRight p f g
  left_projection : leftHomotopy.h ≫ (f ≫ p) =
    ((relativePathBoundaryEndpoint A 0 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ modelBase.h
  right_projection : rightHomotopy.h ≫ (g ≫ p) =
    ((relativePathBoundaryEndpoint A 1 ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ modelBase.h
  path_projection : ((relativePathBoundarySide A ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ modelBase.h =
    (snd (Δ[1] : SSet.{u}) (A : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      boundaryHomotopy.h ≫ fiberwiseIntervalPullbackProjection p f g

end SerrePositivity.InfinityCategories.F2
