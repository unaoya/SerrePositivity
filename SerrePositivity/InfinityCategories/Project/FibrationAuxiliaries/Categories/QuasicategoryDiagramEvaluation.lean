module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramMixedHom

/-!
概要：元の図式の全変換の core の混合作用を、一つの底の対象で評価する。
方針：底の恒等射の混合作用を同じ対象成分の評価へ戻す。
規約：元の豊穣 Hom の全高次を保持する。
使われ方：Cat∞ 値の実現の対象での評価と区間族の端点の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 底の恒等射での同じ混合作用は、元の対象成分への core の射。 -/
lemma quasicategoryDiagramMixedHom_base_id {C : Type u} [Category.{u} C]
    (F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom (𝟙 c) F G =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramCoreEvaluationEnriched c).map F G := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (𝟙 c)
    (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom, (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget).map_id,
    (ihom _).map_id, Category.comp_id]
  rfl

/-- 対象ごとの同じ全高次の評価を、Cat∞ への射として実現する。 -/
def quasicategoryDiagramInfinityEvaluation {C : Type u} [Category.{u} C] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramNerve C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramCoreEvaluationEnriched c)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
