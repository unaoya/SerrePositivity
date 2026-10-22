module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedPullbackIso
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedConstantNaturality

/-!
概要：元の各段の twisted-arrow 引き戻しを、元の weighted 全空間の同じ引き戻しへ含める。
方針：同じ係数包含と、両射影を保つ元の引き戻し同型を合成する。
規約：両射影を厳密に保持。使われ方：指定された全密度評価の係数への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)

/-- 元の各段の同じ twisted-arrow 終点の族を、元の weighted 全族へ含める。 -/
def weightedTwistedCoefficientIntoTotal : pullback (edgewiseRight C) (F.obj i).val.hom ⟶
    pullback (edgewiseRight C)
      (weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι) :=
  weightedNerveConstantLift (strictRightTwistedElementsDiagram F) i ≫
    (weightedTwistedPullbackIso F).hom

lemma weightedTwistedCoefficientIntoTotal_fst :
    weightedTwistedCoefficientIntoTotal F i ≫ pullback.fst _ _ =
      pullback.fst (edgewiseRight C) (F.obj i).val.hom := by
  rw [weightedTwistedCoefficientIntoTotal, Category.assoc, weightedTwistedPullbackIso_fst F]
  exact weightedNerveConstantLift_parameter (strictRightTwistedBaseProjection F) i

lemma weightedTwistedCoefficientIntoTotal_snd :
    weightedTwistedCoefficientIntoTotal F i ≫ pullback.snd _ _ =
      pullback.snd (edgewiseRight C) (F.obj i).val.hom ≫
        weightedNerveConstantLift (rightFibrationTotalDiagram F) i := by
  rw [weightedTwistedCoefficientIntoTotal, Category.assoc, weightedTwistedPullbackIso_snd F]
  exact weightedConstantLift_naturality (strictRightTwistedTotalProjection F) i

end SerrePositivity.InfinityCategories.F2.Ind
