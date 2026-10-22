module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedElementsPullback
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientIntoTotal

/-!
概要：元の係数 twisted-arrow 族は、元の全 weighted 族の同じ係数包含での引き戻し。
方針：元の二つの Hom 引き戻しを貼り、元の係数包含の両射影の公式で右側を消去。
規約：元の係数写像そのもの。使われ方：元の共同復元の係数制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)

/-- 始点を保持して元の係数全空間を、元の weighted 全空間へ含める。 -/
def weightedTwistedCoefficientBaseInclusion : C.op ⊗ (F.obj i).val.left ⟶
    C.op ⊗ weightedNerve (rightFibrationTotalDiagram F) :=
  lift (fst _ _) (snd _ _ ≫ weightedNerveConstantLift (rightFibrationTotalDiagram F) i)

/-- 元の係数包含は、元の Hom の共同底を厳密に保つ。 -/
lemma weightedTwistedCoefficientBaseInclusion_base :
    weightedTwistedCoefficientBaseInclusion F i ≫ twistedElementsBaseMap
      (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) =
        twistedElementsBaseMap (F.obj i).val.hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, weightedTwistedCoefficientBaseInclusion,
      twistedElementsBaseMap, lift_fst]
  · simp only [Category.assoc, weightedTwistedCoefficientBaseInclusion,
      twistedElementsBaseMap, lift_snd, lift_snd_assoc]
    rw [weightedNerveConstantLift_parameter]
    rfl

/-- 元の twisted-arrow 係数包含は、元の共同射影と厳密に可換する。 -/
lemma weightedTwistedCoefficientIntoTotal_projection :
    weightedTwistedCoefficientIntoTotal F i ≫ twistedElementsProjection
      (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) =
      twistedElementsProjection (F.obj i).val.hom ≫
        weightedTwistedCoefficientBaseInclusion F i := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, twistedElementsProjection,
      weightedTwistedCoefficientBaseInclusion, lift_fst]
    rw [← Category.assoc, weightedTwistedCoefficientIntoTotal_fst]
  · simp only [Category.assoc, twistedElementsProjection,
      weightedTwistedCoefficientBaseInclusion, lift_snd, lift_snd_assoc]
    rw [weightedTwistedCoefficientIntoTotal_snd]

/-- 元の twisted-arrow 係数族は、元の共同射影の同じ係数包含での引き戻し。 -/
lemma weightedTwistedCoefficientIntoTotal_isPullback :
    IsPullback (weightedTwistedCoefficientIntoTotal F i)
      (twistedElementsProjection (F.obj i).val.hom)
      (twistedElementsProjection
        (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι))
      (weightedTwistedCoefficientBaseInclusion F i) := by
  apply IsPullback.of_right _ (weightedTwistedCoefficientIntoTotal_projection F i)
    (twistedElements_isPullback
      (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι))
  rw [weightedTwistedCoefficientIntoTotal_fst, weightedTwistedCoefficientBaseInclusion_base]
  exact twistedElements_isPullback (F.obj i).val.hom

end SerrePositivity.InfinityCategories.F2.Ind
