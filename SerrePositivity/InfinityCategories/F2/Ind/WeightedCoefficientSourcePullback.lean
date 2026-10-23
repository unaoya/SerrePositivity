module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientPullback
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluationRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedSourceElementsBaseChange

/-!
概要：元の係数の始点固定族は、元の全 weighted 共同射影の同じ係数・始点での引き戻し。
方針：元の係数引き戻しと、元の始点固定の引き戻しを貼り合わせる。
規約：元の族・包含・底を固定。使われ方：同じ共同復元の評価図式への底変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)

/-- 元の係数の始点固定族を、元の全 weighted twisted-arrow 族へ含める。 -/
def weightedCoefficientSourceIntoTotal : twistedSourceElements (F.obj i).val.hom x ⟶
    pullback (edgewiseRight C) (weightedDensityProjection F) :=
  twistedSourceElementsComparison (F.obj i).val.hom x ≫ weightedTwistedCoefficientIntoTotal F i

/-- 元の係数・始点包含は、元の共同射影の同じ引き戻しを与える。 -/
lemma weightedCoefficientSourceIntoTotal_isPullback :
    IsPullback (weightedCoefficientSourceIntoTotal F i x)
      (pullback.fst (F.obj i).val.hom (twistedArrowSourceProjection x))
      (twistedElementsProjection (weightedDensityProjection F))
      (weightedCoefficientEvaluationBase F i x) := by
  have hs : IsPullback (twistedSourceElementsComparison (F.obj i).val.hom x)
      (pullback.fst (F.obj i).val.hom (twistedArrowSourceProjection x))
      (twistedElementsProjection (F.obj i).val.hom)
      (lift (SSet.const (SSet.opObjEquiv.symm x)) (𝟙 (F.obj i).val.left)) :=
    IsPullback.of_iso_pullback ⟨twistedSourceElementsComparison_projection (F.obj i).val.hom x⟩
      (twistedSourceElementsBaseChangeIso (F.obj i).val.hom x)
      (twistedSourceElementsBaseChangeIso_fst (F.obj i).val.hom x)
      (twistedSourceElementsBaseChangeIso_snd (F.obj i).val.hom x)
  have h := hs.paste_horiz (weightedTwistedCoefficientIntoTotal_isPullback F i)
  have hb : lift (SSet.const (SSet.opObjEquiv.symm x)) (𝟙 (F.obj i).val.left) ≫
      weightedTwistedCoefficientBaseInclusion F i = weightedCoefficientEvaluationBase F i x := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, weightedTwistedCoefficientBaseInclusion,
        weightedCoefficientEvaluationBase, lift_fst]
    · simp only [Category.assoc, weightedTwistedCoefficientBaseInclusion,
        weightedCoefficientEvaluationBase, lift_snd, lift_snd_assoc, Category.id_comp]
  rw [hb] at h
  exact h

/-- 同じ元の包含は、同じ評価の元の全空間成分を厳密に保つ。 -/
lemma weightedCoefficientSourceIntoTotal_projection :
    weightedCoefficientSourceIntoTotal F i x ≫
      twistedElementsProjection (weightedDensityProjection F) =
      pullback.fst (F.obj i).val.hom (twistedArrowSourceProjection x) ≫
        weightedCoefficientEvaluationBase F i x :=
  (weightedCoefficientSourceIntoTotal_isPullback F i x).w

end SerrePositivity.InfinityCategories.F2.Ind
