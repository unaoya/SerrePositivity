module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightTwistedDiagram
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightWeightedClassification

/-!
概要：元の twisted-arrow 全族の左端を、共同 weighted 分類の元の全空間へ送る。
方針：自然な左端射影を weighted nerve に写し、底と添字の両射影を検査する。
規約：元の全図式と同じ評価写像を保持。使われ方：大域密度の指定変換への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 全添字を同時に動かす、元の twisted arrow の反転した左端。 -/
def strictRightTwistedLeftEvaluation : strictRightTwistedTotalDiagram F ⟶
    leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C) where
  app i := edgewiseLeft (F.obj i).val.left
  naturality _ _ f := edgewiseLeft_naturality (F.map f).left

/-- 同じ左端評価は、各段で元の反転した底への射影を保つ。 -/
lemma strictRightTwistedLeftEvaluation_projection (i : I) :
    (strictRightTwistedLeftEvaluation F).app i ≫
      (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)).app i =
        edgewiseSubdivisionMap (F.obj i).val.hom ≫ edgewiseLeft C :=
  (edgewiseLeft_naturality (F.obj i).val.hom).symm

/-- 同じ全族の左端評価は、元の共同 weighted 全空間への一つの射を与える。 -/
def weightedRightTwistedEvaluation : weightedNerve (strictRightTwistedTotalDiagram F) ⟶
    weightedNerve (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C)) :=
  weightedNerveMap (strictRightTwistedLeftEvaluation F)

/-- 同じ全評価は、共同分類の元の底と元の添字を厳密に保つ。 -/
lemma weightedRightTwistedEvaluation_projection :
    weightedRightTwistedEvaluation F ≫
      leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C) =
        weightedNerveParameterProjection (strictRightTwistedLeftEvaluation F ≫
          leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, leftFibrationWeightedProjection,
      weightedNerveParameterProjection, lift_fst, weightedNerveParameter,
      weightedNerveMap_comp, weightedRightTwistedEvaluation]
  · simp only [Category.assoc, leftFibrationWeightedProjection,
      weightedNerveParameterProjection, lift_snd, weightedRightTwistedEvaluation,
      weightedNerveMap_projection]

end SerrePositivity.InfinityCategories.F2.Ind
