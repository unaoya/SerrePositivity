module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackFiberCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackFiberInverse
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：値の包含の第一入力は元の第一 fiber の包含。
方針：逆射の第一脚と fiber の包含式を合成する。
規約：元の第一値。使われ方：元の値の余錐の第一脚の照合。 -/
lemma fiberwisePullbackValueToTotal_left :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) b := by
  change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberInverse p f g b ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberInverse_left]

/-- 概要：値の包含の第二入力は元の第二 fiber の包含。
方針：逆射の第二脚と fiber の包含式を合成する。
規約：元の第二値。使われ方：元の値の余錐の第二脚の照合。 -/
lemma fiberwisePullbackValueToTotal_right :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) b := by
  change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberInverse p f g b ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberInverse_right]

/-- 概要：値の包含の全 path は元の標的 fiber の包含で写した元の全 path。
方針：逆射の path 座標と内部 Hom への包含式を合成する。
規約：両端だけでなく全単体を保持。使われ方：元の指定比較ホモトピーの照合。 -/
lemma fiberwisePullbackValueToTotal_path :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g ≫
      pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ≫
          (ihom (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberInverse p f g b ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberInverse_path]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
