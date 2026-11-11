module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldLargeBridge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexStandardOverIsos

/-!
概要：大きい Segal 表示の二成分と共有頂点を、元のセルの持ち上げと底上で同一視する。
方針：同じ比較の射影式と、標準単体・有限鎖の宇宙同型を使う。
規約：元のセルと共有頂点への両脚を厳密に保持する。
使われ方：高次単体の元の分類先の制限と局所 Hom 比較の接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge n k

/-- 最初の区間の標準表示と元の最初の辺の、同じ底上の同型。 -/
def cocartesianScaffoldLargeFirstOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.first n H ≅ Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k))) :=
  Over.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge_inl n k).symm

/-- 尾部の大きい nerve 表示と元の尾部の、同じ底上の同型。 -/
def cocartesianScaffoldLargeTailOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.tail n H ≅ Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k))) :=
  Over.isoMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso.{u} n) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge_inr n k).symm

/-- 一つの共有頂点の標準表示と元の共有セルの、同じ底上の同型。 -/
def cocartesianScaffoldLargeSharedOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.vertex n H ≅ Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k))) :=
  Over.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 0) (by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso_cell_comp (SimplexCategory.δ (0 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k)).trans
      (congrArg (fun m ↦ stdSimplex.δ (0 : Fin 2) ≫ m)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge_inl n k).symm))

/-- 表示同型は、元の最初の辺への同じ共有頂点の脚を保つ。 -/
lemma cocartesianScaffoldLargeOverIso_first :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.toFirst n H ≫ (cocartesianScaffoldLargeFirstOverIso n k).hom =
      (cocartesianScaffoldLargeSharedOverIso n k).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedToFirst n k) := by
  apply Over.OverMorphism.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_large_projection (SimplexCategory.δ (0 : Fin 2))).symm

/-- 表示同型は、元の尾部への同じ共有頂点の脚も保つ。 -/
lemma cocartesianScaffoldLargeOverIso_tail :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.toTail n H ≫ (cocartesianScaffoldLargeTailOverIso n k).hom =
      (cocartesianScaffoldLargeSharedOverIso n k).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedToTail n k) := by
  apply Over.OverMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso_point n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
