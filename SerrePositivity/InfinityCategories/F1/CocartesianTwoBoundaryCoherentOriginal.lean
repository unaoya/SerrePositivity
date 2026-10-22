module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryGlobalPullbackComparison

/-!
概要：実際の二次元標準境界の coherent な比較を、元の大域 Hom 作用へ戻す。
方針：同じ pullback 上の大域同型に分類先の表示同型の逆を後合成する。
規約：元の全 Hom・同じ境界比較・元の分類主写像を保持する。
使われ方：境界固定の局所比較と高次セルへの帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ coherent な実際の境界比較は、元の全 Hom 作用の境界制限と指定同型で結ばれる。 -/
def cocartesianTwoBoundaryCoherentHomComparison_originalIso :
    FunctorIso
      (cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom (HornBoundaryOver.apex 1 σ) ≫
        cocartesianTwoBoundaryCoherentHomComparison j p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramGlobalDiagramRestriction P Q (HornBoundaryOver.apex 1 σ)) := by
  apply F2.functorIsoOfEq ((cocartesianTwoBoundaryGlobalPullbackComparisonIso j p q).postcomp
    (cocartesianTwoBoundaryTargetPresentationIso p q).inv)
  · dsimp only [cocartesianTwoBoundaryCorrectedGlobalPullbackMap]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · dsimp only [cocartesianTwoBoundaryOriginalGlobalPullbackMap]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
