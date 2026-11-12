module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CylinderBoundaryMono
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathComparisonFaces
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTransportTarget

/-!
概要：相対 path 比較正方形を元の二入力の全円柱を持つ通常の正方形へ移す。
方針：path とパラメータを交換し、二端点で元の輸送円柱と照合する。
規約：時間を交換しない。使われ方：元の Kan 引き戻し内のホモトピーの構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の二入力の全円柱は通常の比較正方形の全二端点に厳密に一致。
方針：直和円柱の両脚と相対比較の両端を計算。
規約：元の入力輸送を保持。使われ方：Kan cospan の正方形持ち上げ。 -/
lemma relativePathComparison_square_boundary {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
    {m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (F : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H)
    (hF : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫
      ((β_ K (Δ[1] : SSet.{u})).hom ▷ (Δ[1] : SSet.{u})) ≫ F =
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinder_hom_ext
  · rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion, coprod.inl_desc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫ F =
      ((coprod.inl : K ⟶ K ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_inl]
    exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathComparison_zero d hk he F hF
  · rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion, coprod.inr_desc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ F =
      ((coprod.inr : K ⟶ K ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_inr]
    exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathComparison_one d hk he F hF

end SerrePositivity.InfinityCategories.Project.FilteredExchange
