module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConstantDiagram
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackFiberInverse
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates

/-!
概要：元の三値の path 引き戻しから全空間への包含は元の三座標を保つ。
方針：fiber 同型の逆の三座標と、元の fiber の包含式を合成する。
規約：全 path は元の標的 fiber の包含で写す。
使われ方：構成済み Kan 比較と元の値の引き戻しの指定データの照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：値の包含の第一入力は元の第一 fiber の包含。
方針：逆射の第一脚と fiber の包含式を合成する。
規約：元の第一値。使われ方：元の値の余錐の第一脚の照合。 -/
lemma fiberwisePullbackValueToTotal_left :
    fiberwisePullbackValueToTotal p f g b ≫ fiberwiseIntervalPullbackLeft p f g =
      intervalPullbackLeft (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) ≫ vertexFiberι (f ≫ p) b := by
  change fiberwisePullbackFiberInverse p f g b ≫
    (vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
      fiberwiseIntervalPullbackLeft p f g) = _
  rw [← fiberwisePullbackFiberLeft_ι, ← Category.assoc, fiberwisePullbackFiberInverse_left]

/-- 概要：値の包含の第二入力は元の第二 fiber の包含。
方針：逆射の第二脚と fiber の包含式を合成する。
規約：元の第二値。使われ方：元の値の余錐の第二脚の照合。 -/
lemma fiberwisePullbackValueToTotal_right :
    fiberwisePullbackValueToTotal p f g b ≫ fiberwiseIntervalPullbackRight p f g =
      intervalPullbackRight (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) ≫ vertexFiberι (g ≫ p) b := by
  change fiberwisePullbackFiberInverse p f g b ≫
    (vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
      fiberwiseIntervalPullbackRight p f g) = _
  rw [← fiberwisePullbackFiberRight_ι, ← Category.assoc, fiberwisePullbackFiberInverse_right]

/-- 概要：値の包含の全 path は元の標的 fiber の包含で写した元の全 path。
方針：逆射の path 座標と内部 Hom への包含式を合成する。
規約：両端だけでなく全単体を保持。使われ方：元の指定比較ホモトピーの照合。 -/
lemma fiberwisePullbackValueToTotal_path :
    fiberwisePullbackValueToTotal p f g b ≫ fiberwiseIntervalPullbackPath p f g ≫
      pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) =
      intervalPullbackPath (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) ≫
          (ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b) := by
  change fiberwisePullbackFiberInverse p f g b ≫
    (vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
      fiberwiseIntervalPullbackPath p f g ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B)) = _
  rw [← fiberwisePullbackFiberPath_ι, ← Category.assoc, fiberwisePullbackFiberInverse_path]

end SerrePositivity.InfinityCategories.F2
