module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPoint
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathValuePoint

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：反映後の指定 path が定める Kan 点は元の一値の実際の比較像。
方針：元の二入力と全 path を保持する三座標の式を使う。
規約：path の端点証明に依存しない。使われ方：相対有限持ち上げの実際の終点。 -/
lemma relativePathValuePoint_kan_point {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
    {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : RelativePathInputTransportData p f g A u v a m q)
    (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ vertexFiber p d.vertex)
    (hr : relativePathBoundaryι A ≫ r = relativePathTransportTargetFiber d)
    (J : SSet.Homotopy
      ((d.leftValue ≫ vertexFiberι (f ≫ p) d.vertex) ≫ f ≫ continuousKanReplacementUnit.app H)
      ((d.rightValue ≫ vertexFiberι (g ≫ p) d.vertex) ≫ g ≫ continuousKanReplacementUnit.app H))
    (hJ : J.h = (β_ K (Δ[1] : SSet.{u})).hom ≫ r ≫ vertexFiberι p d.vertex ≫
      continuousKanReplacementUnit.app H) :
    kanCospanPoint f g (d.leftValue ≫ vertexFiberι (f ≫ p) d.vertex)
      (d.rightValue ≫ vertexFiberι (g ≫ p) d.vertex) J =
        relativePathValuePoint d r hr ≫ fiberwisePullbackValueKanComparison p f g d.vertex := by
  apply intervalPullback_hom_ext
  · rw [kanCospanPoint_path, hJ]
    rw [Category.assoc, fiberwisePullbackValueKanComparison_path]
    rw [← Category.assoc (relativePathValuePoint d r hr), relativePathValuePoint_path,
      ← curry_natural_right]
    rfl
  · rw [Category.assoc, fiberwisePullbackValueKanComparison_left,
      ← Category.assoc, relativePathValuePoint_left, kanCospanPoint_left]
    rfl
  · rw [Category.assoc, fiberwisePullbackValueKanComparison_right,
      ← Category.assoc, relativePathValuePoint_right, kanCospanPoint_right]
    rfl

end SerrePositivity.InfinityCategories.F2
