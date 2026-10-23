module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathComparisonFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CylinderBoundaryMono

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の二入力の全円柱は通常の比較正方形の全二端点に厳密に一致。
方針：直和円柱の両脚と相対比較の両端を計算。
規約：元の入力輸送を保持。使われ方：Kan cospan の正方形持ち上げ。 -/
lemma relativePathComparison_square_boundary {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
    {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : RelativePathInputTransportData p f g A u v a m q)
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (F : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj H)
    (hF : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ F =
      (relativePathBoundaryTransportHomotopy d hk he).h ≫ continuousKanReplacementUnit.app H) :
    (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫
      ((β_ K (Δ[1] : SSet.{u})).hom ▷ (Δ[1] : SSet.{u})) ≫ F =
        coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
          continuousKanReplacementUnit.app H := by
  apply coprodCylinder_hom_ext
  · rw [← comp_whiskerRight_assoc, cylinderBoundaryInclusion, coprod.inl_desc]
    change (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫ F =
      ((coprod.inl : K ⟶ K ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫
        coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
          continuousKanReplacementUnit.app H
    rw [← Category.assoc, coprodCylinderMap_inl]
    exact relativePathComparison_zero d hk he F hF
  · rw [← comp_whiskerRight_assoc, cylinderBoundaryInclusion, coprod.inr_desc]
    change (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ F =
      ((coprod.inr : K ⟶ K ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫
        coprodCylinderMap (d.leftHomotopy.h ≫ f) (d.rightHomotopy.h ≫ g) ≫
          continuousKanReplacementUnit.app H
    rw [← Category.assoc, coprodCylinderMap_inr]
    exact relativePathComparison_one d hk he F hF

end SerrePositivity.InfinityCategories.F2
