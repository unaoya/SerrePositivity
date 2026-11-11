module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTwistedNativeBase

/-!
概要：全添字の相対評価を、元の weighted 密度の twisted-arrow 引き戻しへ移す。
方針：元の両射影を保つ同型の逆で同じ全評価を前合成する。
規約：共同底と元の制限評価を保持。使われ方：共同 Hom の unstraightening への実際の相対射。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- 元の weighted 密度の同じ twisted-arrow 引き戻し上の全評価。 -/
def weightedTwistedNativeLift :
    Limits.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (B := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedPullbackIso F).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceLift F).map

/-- 移した同じ評価は、元の共同 Hom の始点と終点添字を厳密に保つ。 -/
lemma weightedTwistedNativeLift_projection :
    weightedTwistedNativeLift F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection (C := C)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (B := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedNativeJointBase F := by
  rw [weightedTwistedNativeLift, Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceLift F).over_base,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedPullbackIso_jointBase F, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- 同じ元の比較で制限すると、同じ全族の指定された評価を回収する。 -/
lemma weightedTwistedNativeLift_restrict :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedRightTwistedComparison F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedPullbackIso F).hom) ≫
      weightedTwistedNativeLift F =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedRightTwistedComparison F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceLift F).map := by
  simp only [weightedTwistedNativeLift, Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
