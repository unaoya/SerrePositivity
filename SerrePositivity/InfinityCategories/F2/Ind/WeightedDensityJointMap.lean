module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedNativeLift
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction

/-!
概要：元の weighted 密度の全評価を、同じ共同分類図式の小さい unstraightening へ移す。
方針：元の共同 left fibration の復元射と厳密な底変換の引き戻しを使う。
規約：共同 Hom の元の底を保持。使われ方：元の全図式に対する一つの coherent 密度変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の共同分類を、元の weighted 全空間の同じ終点添字で評価する全図式。 -/
def weightedDensityJointTargetDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ weightedNerve (rightFibrationTotalDiagram F)) ⟶
      SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedTwistedNativeJointBase F) ≫
    leftStraighteningInfinityDiagram
      (leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C))

variable [Quasicategory C]
local instance : Quasicategory (C.op ⊗ nerve I) :=
  quasicategory_of_innerFibration (fst C.op (nerve I))

/-- 元の twisted-arrow 全評価に対応する、同じ共同 Hom の底上の実際の射。 -/
def weightedDensityTwistedJointMap :
    pullback (edgewiseRight C)
      (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) ⟶
      smallLeftUnstraightening (weightedDensityJointTargetDiagram F) :=
  (smallLeftUnstraighteningMap_isPullback (weightedDensityJointTargetDiagram F)
    (leftStraighteningInfinityDiagram
      (leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C)))
    (weightedTwistedNativeJointBase F) rfl).lift
      (weightedTwistedNativeLift F ≫ leftStraighteningInfinityReconstruction
        (leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C)))
      (twistedElementsProjection (C := C)
        (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι)) (by
          rw [Category.assoc, leftStraighteningInfinityReconstruction_projection,
            weightedTwistedNativeLift_projection])

/-- 同じ全評価は、元の共同 Hom の射影を厳密に保つ。 -/
lemma weightedDensityTwistedJointMap_projection :
    weightedDensityTwistedJointMap F ≫
      smallLeftUnstraighteningProjection (weightedDensityJointTargetDiagram F) =
        twistedElementsProjection (C := C)
          (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) :=
  (smallLeftUnstraighteningMap_isPullback (weightedDensityJointTargetDiagram F)
    (leftStraighteningInfinityDiagram
      (leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C)))
    (weightedTwistedNativeJointBase F) rfl).lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
