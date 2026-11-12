module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCellCospan
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOverPushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexSmallStandardOverIsos

/-!
概要：小さい Segal 表示の最初の区間と尾部を、同じ元のセルと底上で同一視する。
方針：同じ比較の二射影と標準単体・有限鎖の同型を使う。
規約：元のセルと一つの共有頂点への両脚を保持する。
使われ方：元の source 制限への全次元の自明 Kan 性の移送。

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

/-- 元の小さい底上で、最初の区間と尾部を貼る同じ比較。 -/
def cocartesianScaffoldSmallBridge := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ≫ nerveMap k
local notation "H" => cocartesianScaffoldSmallBridge n k

/-- 最初の標準区間と元の最初の辺の、同じ底上の同型。 -/
def cocartesianScaffoldSmallFirstOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.first n H ≅ Over.mk (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k)) :=
  Over.isoMk (stdSimplex.isoNerve.{u} 1) (by
    change _ = pushout.inl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ≫ nerveMap k)
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inl, Category.assoc]
    rfl)

/-- 尾部の表示は同じ元の尾部そのものであり、底上で同型。 -/
def cocartesianScaffoldSmallTailOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.tail n H ≅ Over.mk (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ _ = pushout.inr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ≫ nerveMap k)
    rw [Category.id_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inr]
    rfl)

/-- 同じ共有頂点の標準表示と元の一つの共有セルの底上の同型。 -/
def cocartesianScaffoldSmallSharedOverIso :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.vertex n H ≅ Over.mk (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k)) :=
  Over.isoMk (stdSimplex.isoNerve.{u} 0) (by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.stdSimplexIsoNerve_cell_comp (SimplexCategory.δ (0 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k)).trans
      (congrArg (fun m ↦ stdSimplex.δ (0 : Fin 2) ≫ m)
        (cocartesianScaffoldSmallFirstOverIso n k).hom.w))

/-- 表示同型は最初の辺への同じ共有頂点の脚を保つ。 -/
lemma cocartesianScaffoldSmallOverIso_first :
    (cocartesianScaffoldSmallSharedOverIso n k).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedToFirst n k =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.toFirst n H ≫ (cocartesianScaffoldSmallFirstOverIso n k).hom := by
  apply Over.OverMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_projection (SimplexCategory.δ (0 : Fin 2))

/-- 表示同型は尾部への同じ共有頂点の脚も保つ。 -/
lemma cocartesianScaffoldSmallOverIso_tail :
    (cocartesianScaffoldSmallSharedOverIso n k).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedToTail n k =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.toTail n H ≫ (cocartesianScaffoldSmallTailOverIso n k).hom := by
  apply Over.OverMorphism.ext
  change (stdSimplex.isoNerve.{u} 0).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _) ≫ 𝟙 _
  rw [Category.comp_id]
  ext d s i
  rfl

/-- 恒等セルの同じ小さい比較は、元の有限鎖への比較そのもの。 -/
lemma cocartesianScaffoldSmallBridge_id :
    cocartesianScaffoldSmallBridge n (𝟭 (ULift.{u} (Fin (n + 2)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ≫ 𝟙 _ = _
  exact Category.comp_id _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
