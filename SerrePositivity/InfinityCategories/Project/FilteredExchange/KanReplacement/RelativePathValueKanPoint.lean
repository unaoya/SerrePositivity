module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathValuePoint

/-!
概要：全相対境界を保つ反映後の path の Kan 点を元の実際の比較像と同定する。
方針：三座標と curry の自然性を照合する。
規約：元の値の射と比較を選び直さない。使われ方：標的引き戻し内の相対比較の終点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：反映後の指定 path が定める Kan 点は元の一値の実際の比較像。
方針：元の二入力と全 path を保持する三座標の式を使う。
規約：path の端点証明に依存しない。使われ方：相対有限持ち上げの実際の終点。 -/
lemma relativePathValuePoint_kan_point {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
    {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
    (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex)
    (hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d)
    (J : SSet.Homotopy
      ((d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) d.vertex) ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      ((d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) d.vertex) ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (hJ : J.h = (β_ K (Δ[1] : SSet.{u})).hom ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g (d.leftValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) d.vertex)
      (d.rightValue ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) d.vertex) J =
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison p f g d.vertex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_path, hJ]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison_path]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr), _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint_path,
      ← curry_natural_right]
    rfl
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison_left,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint_left, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_left]
    rfl
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison_right,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint_right, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_right]
    rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
