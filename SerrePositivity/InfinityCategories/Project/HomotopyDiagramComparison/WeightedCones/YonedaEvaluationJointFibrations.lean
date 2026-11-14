module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.YonedaEvaluationJoint
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.UniverseUnstraightening

/-!
概要：元の共同 Yoneda Hom と共同評価を、同じ元の底上の実 left fibration で表現する。
方針：元の twisted arrow 射影を引き戻し、元の評価の unstraightening と比較する準備。
規約：底と全空間と全分類図式を固定する。未構成の比較射を入力に置いて完成としない。
使われ方：全 C・全前層の Yoneda 評価比較を与える、同じ底上の大域射の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の両変数の底は、元の C が quasicategory なら quasicategory。 -/
instance yonedaEvaluationJointBase_quasicategory (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase C) :=
  quasicategory_of_innerFibration
    (CartesianMonoidalCategory.fst ((SSet.uliftFunctor.{u + 1, u}).obj C.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C))

/-- 元の共同 Yoneda Hom の全空間。元の twisted arrow 射影の厳密な引き戻し。 -/
def yonedaHomJointTotal (C : SSet.{u}) [Quasicategory C] : SSet.{u + 1} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointBaseMap C)

/-- 元の共同 Yoneda Hom 全空間の、同じ元の両変数の底への射影。 -/
def yonedaHomJointProjection (C : SSet.{u}) [Quasicategory C] :
    yonedaHomJointTotal C ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase C := pullback.snd _ _

/-- 元の共同 Hom の実際の射影は left fibration。 -/
instance yonedaHomJointProjection_leftFibration (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (yonedaHomJointProjection C) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem
    (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)))⟩

/-- 元の共同 Hom 全空間の分類は、同じ指定共同 Hom 図式と全自然同型。 -/
def yonedaHomJoint_classificationIso (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (yonedaHomJointProjection C))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointDiagram C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointBaseMap C)).symm

/-- 元の共同評価の全空間。元の評価図式の実際の unstraightening。 -/
def yonedaEvaluationJointTotal (C : SSet.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C)

/-- 元の共同評価の実際の全空間射影は、同じ元の両変数の底を持つ。 -/
def yonedaEvaluationJointProjection (C : SSet.{u}) :
    yonedaEvaluationJointTotal C ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C)

/-- 元の共同評価の実際の射影は left fibration。 -/
instance yonedaEvaluationJointProjection_leftFibration (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (yonedaEvaluationJointProjection C) :=
  inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C)))

/-- 元の共同評価全空間の分類は、同じ指定宇宙変更をした共同評価と全自然同型。 -/
def yonedaEvaluationJoint_classificationIso (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (yonedaEvaluationJointProjection C))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointDiagram C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseUnstraightening_classificationIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
