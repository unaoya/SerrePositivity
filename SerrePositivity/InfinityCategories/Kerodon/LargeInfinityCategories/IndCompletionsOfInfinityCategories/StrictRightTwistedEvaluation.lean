module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightTwistedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightWeightedClassification

/-!
概要：元の twisted-arrow 全族の左端を、共同 weighted 分類の元の全空間へ送る。
方針：自然な左端射影を weighted nerve に写し、底と添字の両射影を検査する。
規約：元の全図式と同じ評価写像を保持。使われ方：大域密度の指定変換への入力。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- 全添字を同時に動かす、元の twisted arrow の反転した左端。 -/
def strictRightTwistedLeftEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedTotalDiagram F ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C) where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (F.obj i).val.left
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality (F.map f).left

/-- 同じ左端評価は、各段で元の反転した底への射影を保つ。 -/
lemma strictRightTwistedLeftEvaluation_projection (i : I) :
    (strictRightTwistedLeftEvaluation F).app i ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)).app i =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.obj i).val.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality (F.obj i).val.hom).symm

/-- 同じ全族の左端評価は、元の共同 weighted 全空間への一つの射を与える。 -/
def weightedRightTwistedEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedTotalDiagram F) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (strictRightTwistedLeftEvaluation F)

/-- 同じ全評価は、共同分類の元の底と元の添字を厳密に保つ。 -/
lemma weightedRightTwistedEvaluation_projection :
    weightedRightTwistedEvaluation F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection (strictRightTwistedLeftEvaluation F ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_comp, weightedRightTwistedEvaluation]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, lift_snd, weightedRightTwistedEvaluation,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
