module

public import SerrePositivity.InfinityCategories.Core.IntervalBoundary
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CylinderBoundaryMono
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPoint
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.KanCospanPointHomotopy
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.PathSquareCurry
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathComparisonSquareBoundary
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathValueKanPoint
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathValuePoint

/-!
概要：全相対境界付き path 比較を、元の Kan 引き戻し内の実際の比較へ移す。
方針：全境界正方形を持ち上げ、終点を元の値の比較像と三座標で同定する。
規約：二入力の円柱と全 path 正方形を保持。使われ方：境界付きの標的有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の一値の実際の比較像へのホモトピーを三座標を保持して構成する。
方針：元の正方形と入力円柱を Kan 引き戻しに入れる。
規約：有限性や追加の持ち上げを仮定しない。使われ方：相対有限比較の標的内の実現。 -/
lemma relativePath_kan_point_comparison {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
    {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : RelativePathInputTransportData p f g A u v a m q)
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ vertexFiber p d.vertex)
    (hr : relativePathBoundaryι A ≫ r = relativePathTransportTargetFiber d)
    (H₀ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H))
    (T : SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h)
      (r ≫ vertexFiberι p d.vertex ≫ continuousKanReplacementUnit.app H))
    (hT : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
      (relativePathBoundaryTransportHomotopy d hk he).h ≫ continuousKanReplacementUnit.app H) :
    ∃ L : SSet.Homotopy (kanCospanPoint f g u v H₀)
      (relativePathValuePoint d r hr ≫ fiberwisePullbackValueKanComparison p f g d.vertex),
      L.h ≫ intervalPullbackLeft (continuousKanReplacement.map f)
        (continuousKanReplacement.map g) = d.leftHomotopy.h ≫ continuousKanReplacementUnit.app E ∧
      L.h ≫ intervalPullbackRight (continuousKanReplacement.map f)
        (continuousKanReplacement.map g) = d.rightHomotopy.h ≫ continuousKanReplacementUnit.app D ∧
      L.h ≫ intervalPullbackPath (continuousKanReplacement.map f)
        (continuousKanReplacement.map g) = pathSquareCurry
          (((β_ K (Δ[1] : SSet.{u})).hom ▷ (Δ[1] : SSet.{u})) ≫ T.h) := by
  let S : SSet.Homotopy H₀.h
      ((β_ K (Δ[1] : SSet.{u})).hom ≫ r ≫ vertexFiberι p d.vertex ≫
        continuousKanReplacementUnit.app H) := functorHomotopyPrecomp T
          (β_ K (Δ[1] : SSet.{u})).hom
  have hS : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ S.h =
      coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
        continuousKanReplacementUnit.app H :=
    relativePathComparison_square_boundary d hk he T.h hT
  obtain ⟨J, hJ, L, hl, hr', hp⟩ := kanCospanPoint_homotopy_of_square f g H₀
    d.leftHomotopy d.rightHomotopy S hS
  have heq := relativePathValuePoint_kan_point d r hr J hJ
  let L' : SSet.Homotopy (kanCospanPoint f g u v H₀)
      (relativePathValuePoint d r hr ≫ fiberwisePullbackValueKanComparison p f g d.vertex) :=
    { h := L.h
      h₀ := L.h₀
      h₁ := by
        change SSet.ι₁ ≫ L.h =
          relativePathValuePoint d r hr ≫ fiberwisePullbackValueKanComparison p f g d.vertex
        rw [L.h₁, heq]
      rel := L.rel }
  exact ⟨L', hl, hr', hp⟩

end SerrePositivity.InfinityCategories.F2
