module

public import SerrePositivity.InfinityCategories.Core.IntervalBoundary
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrismHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalBoundaryHomotopy
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.RelativePathBoundaryCylinderCompatibility
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathBoundaryTransportProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathTransportTarget

/-!
概要：全相対境界を保持する比較正方形の path 両端と指定部分を読む。
方針：元の境界包含の合成式と押し出し円柱の制限式。
規約：全時刻の厳密な等式。使われ方：Kan 引き戻し内の相対比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)
  (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
  (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g))
  (F : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj H)
  (hF : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ F =
    (relativePathBoundaryTransportHomotopy d hk he).h ≫ continuousKanReplacementUnit.app H)
include hF

/-- 概要：比較正方形の両端は元の二入力の全輸送。
方針：全境界の第二脚へ制限。規約：時間を保持。使われ方：引き戻しの入力条件。 -/
lemma relativePathComparison_ends :
    (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ F =
      (relativePathEndsHomotopy d).h ≫ continuousKanReplacementUnit.app H := by
  rw [← relativePathBoundaryEnds_ι A, comp_whiskerRight, Category.assoc, hF,
    ← Category.assoc, relativePathBoundaryTransportHomotopy_ends]

/-- 概要：比較正方形の始点は元の第一入力の全輸送。
方針：区間境界の零端へ制限。規約：時間を保持。使われ方：第一座標の条件。 -/
lemma relativePathComparison_zero :
    (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫ F =
      d.leftHomotopy.h ≫ f ≫ continuousKanReplacementUnit.app H := by
  rw [← intervalBoundaryEndpoint_ι 0 K, comp_whiskerRight, Category.assoc,
    relativePathComparison_ends d hk he F hF, ← Category.assoc]
  change ((intervalBoundaryEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
    (intervalBoundaryHomotopy (functorHomotopyPostcomp d.leftHomotopy f)
      (functorHomotopyPostcomp d.rightHomotopy g)).h) ≫ continuousKanReplacementUnit.app H = _
  rw [intervalBoundaryHomotopy_zero]
  rfl

/-- 概要：比較正方形の終点は元の第二入力の全輸送。
方針：区間境界の一端へ制限。規約：時間を保持。使われ方：第二座標の条件。 -/
lemma relativePathComparison_one :
    (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ F =
      d.rightHomotopy.h ≫ g ≫ continuousKanReplacementUnit.app H := by
  rw [← intervalBoundaryEndpoint_ι 1 K, comp_whiskerRight, Category.assoc,
    relativePathComparison_ends d hk he F hF, ← Category.assoc]
  change ((intervalBoundaryEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
    (intervalBoundaryHomotopy (functorHomotopyPostcomp d.leftHomotopy f)
      (functorHomotopyPostcomp d.rightHomotopy g)).h) ≫ continuousKanReplacementUnit.app H = _
  rw [intervalBoundaryHomotopy_one]
  rfl

/-- 概要：比較正方形の指定部分は元の境界引き戻し円柱の全 path 正方形。
方針：全境界の第一脚へ制限。規約：全 path・全時間。使われ方：相対比較の path 条件。 -/
lemma relativePathComparison_side :
    (((Δ[1] : SSet.{u}) ◁ A.ι) ▷ (Δ[1] : SSet.{u})) ≫ F =
      (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h ≫
        continuousKanReplacementUnit.app H := by
  rw [← relativePathBoundarySide_ι A, comp_whiskerRight, Category.assoc, hF,
    ← Category.assoc, relativePathBoundaryTransportHomotopy_side]

end SerrePositivity.InfinityCategories.F2
