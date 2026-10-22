module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedConstantNaturality

/-!
概要：全添字の twisted-arrow 評価を各段へ制限し、元の同じ左端評価との相対同型を保つ。
方針：係数包含の自然性と、元の全評価の相対同型の前合成を使う。
規約：個々の変換を選び直さない。使われ方：指定された fiber 密度変換の普遍性の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)

/-- 元の全相対比較の係数制限は、元の right fibration の相対右端比較そのもの。 -/
lemma weightedRightTwistedComparison_coefficient :
    weightedNerveConstantLift (strictRightTwistedTotalDiagram F) i ≫
      weightedRightTwistedComparison F =
        relativeEdgewiseRightComparison (F.obj i).val.hom ≫
          weightedNerveConstantLift (strictRightTwistedElementsDiagram F) i :=
  weightedConstantLift_naturality (strictRightTwistedComparison F) i

/-- 元の全左端評価の係数制限は、元の全 twisted arrow の左端射影そのもの。 -/
lemma weightedRightTwistedEvaluation_coefficient :
    weightedNerveConstantLift (strictRightTwistedTotalDiagram F) i ≫
      weightedRightTwistedEvaluation F =
        edgewiseLeft (F.obj i).val.left ≫ weightedNerveConstantLift
          (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C)) i :=
  weightedConstantLift_naturality (strictRightTwistedLeftEvaluation F) i

variable [Quasicategory C]
local notation "p" => leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C)
local notation "r" => weightedRightTwistedComparison F
local notation "b" => weightedTwistedSourceBase F
local notation "c" => weightedNerveConstantLift (strictRightTwistedTotalDiagram F) i

/-- 同じ全族の相対持ち上げは、各段で元の全 twisted-arrow 左端評価と相対同型。 -/
def weightedTwistedSourceLift_coefficientIso : VertexIso
    (relativeFunctorVertex p (c ≫ (r ≫ b))
      (c ≫ (r ≫ (weightedTwistedSourceLift F).map)) (by
        rw [Category.assoc, Category.assoc, (weightedTwistedSourceLift F).over_base]))
    (relativeFunctorVertex p (c ≫ (r ≫ b))
      (edgewiseLeft (F.obj i).val.left ≫ weightedNerveConstantLift
        (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C)) i) (by
          rw [← weightedRightTwistedEvaluation_coefficient F i, Category.assoc,
            weightedRightTwistedEvaluation_over F])) := by
  have he := VertexIso.map (weightedTwistedSourceLift F).evaluationIso
    (relativeFunctorPre p (r ≫ b) c)
  simpa only [relativeFunctorPre_vertex, weightedRightTwistedEvaluation_coefficient F i] using he

end SerrePositivity.InfinityCategories.F2.Ind
