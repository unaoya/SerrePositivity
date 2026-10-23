module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathTargetFiberCoordinates

/-!
概要：全相対境界を保持する元の値内の path の両端を、元の二入力の値で読む。
方針：相対境界の端点を通して制限し、輸送先の厳密な端点式を使う。
規約：path の全相対境界を変更しない。
使われ方：元の値の path 引き戻しへの厳密な持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)
  (z : (Δ[1] : SSet.{u}) ⊗ K ⟶ vertexFiber p d.vertex)
  (hz : relativePathBoundaryι A ≫ z = relativePathTransportTargetFiber d)
include hz

/-- 概要：元の値の path の始点は元の第一値の像。
方針：相対境界の始点で制限する。規約：厳密な式。使われ方：元の値の第一端点条件。 -/
lemma relativePathFiberPath_zero :
    prismEndpoint 0 K ≫ z = d.leftValue ≫ vertexFiberMap (f ≫ p) p f rfl d.vertex := by
  rw [← relativePathBoundaryEndpoint_ι A 0, Category.assoc, hz,
    relativePathTransportTargetFiber_zero]

/-- 概要：元の値の path の終点は元の第二値の像。
方針：相対境界の終点で制限する。規約：厳密な式。使われ方：元の値の第二端点条件。 -/
lemma relativePathFiberPath_one :
    prismEndpoint 1 K ≫ z = d.rightValue ≫ vertexFiberMap (g ≫ p) p g rfl d.vertex := by
  rw [← relativePathBoundaryEndpoint_ι A 1, Category.assoc, hz,
    relativePathTransportTargetFiber_one]

end SerrePositivity.InfinityCategories.F2
