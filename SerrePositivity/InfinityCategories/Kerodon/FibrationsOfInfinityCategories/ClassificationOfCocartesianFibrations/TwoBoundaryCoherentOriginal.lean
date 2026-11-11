module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryGlobalPullbackComparison

/-!
概要：実際の二次元標準境界の coherent な比較を、元の大域 Hom 作用へ戻す。
方針：同じ pullback 上の大域同型に分類先の表示同型の逆を後合成する。
規約：元の全 Hom・同じ境界比較・元の分類主写像を保持する。
使われ方：境界固定の局所比較と高次セルへの帰納。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (j : Fin 2) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ coherent な実際の境界比較は、元の全 Hom 作用の境界制限と指定同型で結ばれる。 -/
def cocartesianTwoBoundaryCoherentHomComparison_originalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 1 σ) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCoherentHomComparison j p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramGlobalDiagramRestriction P Q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 1 σ)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryGlobalPullbackComparisonIso j p q).postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoBoundaryTargetPresentation.cocartesianTwoBoundaryTargetPresentationIso p q).inv)
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryCorrectedGlobalPullbackMap]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoBoundaryOriginalGlobalPullbackMap]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
