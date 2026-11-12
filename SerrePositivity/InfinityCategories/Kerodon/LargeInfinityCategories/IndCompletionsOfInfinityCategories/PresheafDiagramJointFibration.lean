module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnderSectionRightDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps

/-!
概要：元の coherent 前層図式の共同評価から、同じ積上の小さい left fibration を作る。
方針：元の図式を uncurry し、積の宇宙持ち上げを戻して小さい unstraightening を取る。
規約：任意の coherent 図式を扱う。底の前層変数を切断で消去しない。
使われ方：同じ図式の strict right fibration 表示と大域比較の始点。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)

/-- 元の全図式の共同評価。全ての高次単体を同じ uncurry で保持する。 -/
def presheafDiagramJointEvaluation :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} C.op (nerve I)).hom ≫ uncurry F

/-- 共同評価の小さい unstraightening の、元の積への射影。 -/
def presheafDiagramJointProjection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (presheafDiagramJointEvaluation F) ⟶ C.op ⊗ nerve I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (presheafDiagramJointEvaluation F)

instance presheafDiagramJointProjection_leftFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (presheafDiagramJointProjection F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection_leftFibration _

/-- 元の coherent 前層図式から構成した、同じ添字の strict right fibration 図式。 -/
def presheafDiagramRightStrict : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionRightStrictDiagram (presheafDiagramJointProjection F)

/-- 元の共同 unstraightening の、指定添字の値への底上の評価。 -/
def presheafDiagramRightEvaluate (i : I) :
    (presheafDiagramRightStrict F).obj i ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionRightFiber (presheafDiagramJointProjection F) i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionRightEvaluate (presheafDiagramJointProjection F) i

instance presheafDiagramRightStrict_quasicategory [Quasicategory C] (i : I) :
    Quasicategory ((presheafDiagramRightStrict F).obj i).val.left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionRightDiagram_quasicategory _ i

/-- 同じ評価射の全空間上の同値性。大域の分類比較は別途必要。 -/
lemma presheafDiagramRightEvaluate_isQCatEquivalence [Quasicategory C] (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (presheafDiagramRightEvaluate F i).left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionRightEvaluate_isQCatEquivalence _ i

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
