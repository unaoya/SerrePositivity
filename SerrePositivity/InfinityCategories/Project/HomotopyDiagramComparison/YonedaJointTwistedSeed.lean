module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointFibrations
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseTwistedArrowProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseLeftClassification

/-!
概要：元の全 twisted arrow から、共同 Yoneda Hom と共同評価の両全空間への射を構成。
方針：元の Yoneda を twisted arrow に適用し、同じ元の全復元射を評価全空間へ送る。
規約：元の全 twisted arrow の全単体と同じ両変数の底を保持する。
使われ方：大域 Yoneda 評価比較射が保持すべき、一つの全恒等点・全射の族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaJointTwistedSeed
local instance {X : SSet.{u}} [Quasicategory X] : Quasicategory (X.op ⊗ X) :=
  quasicategory_of_innerFibration (CartesianMonoidalCategory.fst X.op X)
variable (C : SSet.{u}) [Quasicategory C]

/-- 元の両端の底を、元の Yoneda と全前層の共同底へ送る元の写像。 -/
def yonedaJointYonedaBaseMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ C) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase C :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op C).hom ≫ (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)

/-- 元の共同評価への同じ写像の制限は、元の共同 Hom の分類図式そのもの。 -/
lemma yonedaJointYonedaBaseMap_evaluation :
    yonedaJointYonedaBaseMap C ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C := by
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op C).hom ≫
    ((((SSet.uliftFunctor.{u + 1, u}).obj C.op) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
      (ihom.ev _).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) = _
  rw [← uncurry_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_uncurry]
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op C).hom_inv_id_assoc _

/-- 元の全 twisted arrow を、同じ両変数の共同底へ送る元の射。 -/
def yonedaJointTwistedBase :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase C :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) ≫ yonedaJointYonedaBaseMap C

/-- 元の全 twisted arrow の Yoneda 像を、元の共同 Hom 全空間へ厳密に持ち上げる。 -/
def yonedaHomJointTwistedSeed :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointTotal C :=
  pullback.lift
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftTwistedArrowIso C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
    (yonedaJointTwistedBase C) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_naturality, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftTwistedArrowIso_projection]
      apply SSet.hom_ext
      intro n
      rfl)

/-- 元の全 twisted arrow の Hom 側の像は、同じ元の共同底を厳密に保つ。 -/
lemma yonedaHomJointTwistedSeed_projection :
    yonedaHomJointTwistedSeed C ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointProjection C = yonedaJointTwistedBase C :=
  pullback.lift_snd _ _ _

/-- 同じ元の全復元射を使い、元の全 twisted arrow を共同評価全空間へ送る。 -/
def yonedaEvaluationJointTwistedSeed :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointTotal C :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftClassificationUniverseComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C)
      (yonedaJointYonedaBaseMap C) (yonedaJointYonedaBaseMap_evaluation C)

/-- 元の全 twisted arrow の評価側の像も、同じ元の共同底を厳密に保つ。 -/
lemma yonedaEvaluationJointTwistedSeed_projection :
    yonedaEvaluationJointTwistedSeed C ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointProjection C =
      yonedaJointTwistedBase C := by
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftClassificationUniverseComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C)
      (yonedaJointYonedaBaseMap C) (yonedaJointYonedaBaseMap_evaluation C)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_projection, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftClassificationUniverseComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C))) ≫
    yonedaJointYonedaBaseMap C = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftClassificationUniverseComparison_projection]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaJointTwistedSeed
