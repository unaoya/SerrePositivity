module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedNativeBase

/-!
概要：全添字の相対評価を、元の weighted 密度の twisted-arrow 引き戻しへ移す。
方針：元の両射影を保つ同型の逆で同じ全評価を前合成する。
規約：共同底と元の制限評価を保持。使われ方：共同 Hom の unstraightening への実際の相対射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の weighted 密度の同じ twisted-arrow 引き戻し上の全評価。 -/
def weightedTwistedNativeLift :
    Limits.pullback (edgewiseRight C)
      (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) ⟶
      weightedNerve (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C)) :=
  (weightedTwistedPullbackIso F).inv ≫ (weightedTwistedSourceLift F).map

/-- 移した同じ評価は、元の共同 Hom の始点と終点添字を厳密に保つ。 -/
lemma weightedTwistedNativeLift_projection :
    weightedTwistedNativeLift F ≫
      leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C) =
        twistedElementsProjection (C := C)
          (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) ≫
            weightedTwistedNativeJointBase F := by
  rw [weightedTwistedNativeLift, Category.assoc, (weightedTwistedSourceLift F).over_base,
    ← weightedTwistedPullbackIso_jointBase F, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- 同じ元の比較で制限すると、同じ全族の指定された評価を回収する。 -/
lemma weightedTwistedNativeLift_restrict :
    (weightedRightTwistedComparison F ≫ (weightedTwistedPullbackIso F).hom) ≫
      weightedTwistedNativeLift F =
        weightedRightTwistedComparison F ≫ (weightedTwistedSourceLift F).map := by
  simp only [weightedTwistedNativeLift, Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
