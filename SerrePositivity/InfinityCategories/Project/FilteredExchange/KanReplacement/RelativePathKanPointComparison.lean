module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CylinderBoundaryMono
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPointHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PathSquareCurry
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathComparisonSquareBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathValueKanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathValuePoint

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の一値の実際の比較像へのホモトピーを三座標を保持して構成する。
方針：元の正方形と入力円柱を Kan 引き戻しに入れる。
規約：有限性や追加の持ち上げを仮定しない。使われ方：相対有限比較の標的内の実現。 -/
lemma relativePath_kan_point_comparison {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
    {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex)
    (hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d)
    (H₀ : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (T : SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h)
      (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (hT : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) :
    ∃ L : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v H₀)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison p f g d.vertex),
      L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = d.leftHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E ∧
      L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = d.rightHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D ∧
      L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry
          (((β_ K (Δ[1] : SSet.{u})).hom ▷ (Δ[1] : SSet.{u})) ≫ T.h) := by
  let S : SSet.Homotopy H₀.h
      ((β_ K (Δ[1] : SSet.{u})).hom ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp T
          (β_ K (Δ[1] : SSet.{u})).hom
  have hS : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ S.h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H :=
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathComparison_square_boundary d hk he T.h hT
  obtain ⟨J, hJ, L, hl, hr', hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_homotopy_of_square f g H₀
    d.leftHomotopy d.rightHomotopy S hS
  have heq := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint_kan_point d r hr J hJ
  let L' : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v H₀)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison p f g d.vertex) :=
    { h := L.h
      h₀ := L.h₀
      h₁ := by
        change SSet.ι₁ ≫ L.h =
          _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison p f g d.vertex
        rw [L.h₁, heq]
      rel := L.rel }
  exact ⟨L', hl, hr', hp⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
