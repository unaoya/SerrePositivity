module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCellCospan
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOverPushout

/-!
概要：最初の辺と尾部の同じ比較を、分類先と同じ宇宙の元の底へ写す。
方針：有限鎖の宇宙比較を後置し、二射影を元のセルの持ち上げへ同定する。
規約：元の通常関手と共有セルを保持する。
使われ方：高次単体で分類先の同じ Segal 制限の自明 Kan 性。

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

/-- 分類先と同じ宇宙の、元のセル上の最初の辺と尾部の比較。 -/
def cocartesianScaffoldLargeBridge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge.{u + 1} n ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso.{u} (n + 1)).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)

/-- 大きい比較の最初の射影は、元の最初の辺の持ち上げ。 -/
lemma cocartesianScaffoldLargeBridge_inl :
    pushout.inl _ _ ≫ cocartesianScaffoldLargeBridge n k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k)) := by
  dsimp only [cocartesianScaffoldLargeBridge]
  rw [← Category.assoc (pushout.inl _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inl,
    Category.assoc, ← Category.assoc (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)),
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso_first]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← CategoryTheory.Functor.map_comp]
  rfl

/-- 大きい比較の尾部射影も、元の尾部セルの持ち上げ。 -/
lemma cocartesianScaffoldLargeBridge_inr :
    pushout.inr _ _ ≫ cocartesianScaffoldLargeBridge n k =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso.{u} n).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k)) := by
  dsimp only [cocartesianScaffoldLargeBridge]
  rw [← Category.assoc (pushout.inr _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inr,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso_tail, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  rfl

/-- 恒等セル上の同じ大きい比較は inner anodyne。 -/
lemma cocartesianScaffoldLargeBridge_id_innerAnodyne :
    innerAnodyneExtensions (cocartesianScaffoldLargeBridge n (𝟭 (ULift.{u} (Fin (n + 2))))) := by
  change innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge.{u + 1} n ≫
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteNerveUniverseIso.{u} (n + 1)).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (𝟙 _))
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact innerAnodyneExtensions.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_innerAnodyne n)
    (innerAnodyneExtensions.of_isIso _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
