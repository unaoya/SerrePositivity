module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathFiberPathEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiberCoordinates

/-!
概要：全相対境界を保つ元の値内の path を、元の値の引き戻しへ厳密に入れる。
方針：元の全 path を curry し、二端点条件で三座標を持ち上げる。
規約：指定部分複体上では元の境界値の射と厳密に一致する。
使われ方：境界付き Kan path 反映を元の一値の引き戻し射へ戻す。
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
  (z : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex)
  (hz : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ z = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d)

/-- 概要：元の値の全 path と二入力を元の値の引き戻しへ入れる。
方針：指定された両端の式で持ち上げる。
規約：全 path を保持。使われ方：元の境界値を保つ相対射。 -/
def relativePathValuePoint : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl d.vertex)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl d.vertex) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift _ _ (curry z) d.leftValue d.rightValue
    (by
      change curry z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathFiberPath_zero d z hz)
    (by
      change curry z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathFiberPath_one d z hz)

/-- 概要：持ち上げの全 path は元の path の curry。
方針：三座標の射影。規約：選び直さない。使われ方：指定境界の path 制限。 -/
lemma relativePathValuePoint_path : relativePathValuePoint d z hz ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl d.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl d.vertex) =
      curry z := by simp only [relativePathValuePoint, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_path]

/-- 概要：持ち上げの第一入力は元の第一値。
方針：三座標の射影。規約：元の入力。使われ方：指定境界の第一脚。 -/
lemma relativePathValuePoint_left : relativePathValuePoint d z hz ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl d.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl d.vertex) =
      d.leftValue := by simp only [relativePathValuePoint, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_left]

/-- 概要：持ち上げの第二入力は元の第二値。
方針：三座標の射影。規約：元の入力。使われ方：指定境界の第二脚。 -/
lemma relativePathValuePoint_right : relativePathValuePoint d z hz ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl d.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl d.vertex) =
      d.rightValue := by simp only [relativePathValuePoint, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_right]

/-- 概要：元の値の引き戻し射は指定部分複体上で元の境界値と厳密に一致。
方針：二入力と全 path の三座標を照合する。
規約：ホモトピーだけでなく等式。使われ方：境界付き相対有限検出の厳密な境界。 -/
lemma relativePathValuePoint_restrict : A.ι ≫ relativePathValuePoint d z hz = d.boundaryValue := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback_hom_ext
  · rw [Category.assoc, relativePathValuePoint_path, ← curry_natural_left,
      ← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide_ι A, Category.assoc, hz, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber_side,
      curry_uncurry]
  · rw [Category.assoc, relativePathValuePoint_left, d.boundary_left]
  · rw [Category.assoc, relativePathValuePoint_right, d.boundary_right]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
