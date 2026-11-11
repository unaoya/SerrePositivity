module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictLeftWeightedClassification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnderSectionClassification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence

/-!
概要：left fibration ∞ 圏の coherent な通常添字の全図式を、同じ添字で strict 化する。
方針：元の分類像の共同評価を復元し、既存の under 切断の全分類比較を curry して戻す。
規約：元の図式との一つの全関手同型を保持し、値ごとの同値で代用しない。
使われ方：有限始域の相対 Hom の一般 coherent filtered 余極限保存。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {B : SSet.{u}} [Quasicategory B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)

/-- 概要：元の分類像を底と添字の両変数で共同評価する。
方針：同じ全図式を uncurry し、積の宇宙持ち上げを比較する。
規約：底 B と通常添字 I の全高次単体を保持する。
使われ方：同じ積上の小さい left fibration の復元。 -/
def leftFibrationDiagramJointEvaluation :
    (SSet.uliftFunctor.{u + 1, u}).obj (B ⊗ nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} B (nerve I)).hom ≫
    uncurry (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B)

/-- 概要：元の共同評価から同じ底上の strict left fibration 図式を構成する。
方針：小さい unstraightening に既存の under 切断構成を適用する。
規約：strict な恒等・合成を持つ同じ通常添字を使う。
使われ方：元の coherent filtered 図式に比較する通常模型。 -/
def leftFibrationDiagramStrictification : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionStrictDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (leftFibrationDiagramJointEvaluation F))

/-- 概要：同じ strict 模型の coherent 実現は元の図式全体と関手同型である。
方針：共同 weighted 分類と復元の余単位を curry し、分類の充満忠実性で戻す。
規約：全添字上の自然性を保持する。
使われ方：任意の指定余錐への strict 模型の余極限保存の移送。 -/
def leftFibrationDiagramStrictificationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (leftFibrationDiagramStrictification F)) F := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (leftFibrationDiagramJointEvaluation F)
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionWeightedProjection p))
      (leftFibrationDiagramJointEvaluation F) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionClassificationIso p).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityCounit (leftFibrationDiagramJointEvaluation F)
  have hc := (h.precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} B (nerve I)).inv).curry
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftWeightedClassification (leftFibrationDiagramStrictification F))
      (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B) := by
    have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (curry ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} B (nerve I)).inv ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionWeightedProjection p)))
        (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B) := by
      simpa only [leftFibrationDiagramJointEvaluation, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp, curry_uncurry] using hc
    exact hc'
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence B).isFullyFaithful.preimageFunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftWeightedClassificationIso (leftFibrationDiagramStrictification F)).symm ≪≫ hw)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
