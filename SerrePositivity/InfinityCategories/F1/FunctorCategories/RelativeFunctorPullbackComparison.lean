module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullbackNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationComparisonBaseChange

/-!
概要：実際の相対 Hom 引き戻しの同値性は、底上の前合成同値による比較で反映される。
方針：始域・標的の置き換えと引き戻しの厳密な自然性に、同値の二対三則を適用する。
規約：二つの底は quasicategory。比較射の同値性は通常の前合成同値で与える。
使われ方：一般の left fibration 対を、復元した coherent unstraightening 対へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 底上の二つの比較が前合成同値なら、比較先での相対引き戻しの同値性を反映する。 -/
lemma relativeFunctorPullback_isQCatEquivalence_of_comparison
    {E E' F F' B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) (p' : E' ⟶ B) (q : F ⟶ B) (q' : F' ⟶ B)
    [LeftFibration p] [LeftFibration p'] [LeftFibration q] [LeftFibration q']
    (i : E ⟶ E') (hi : i ≫ p' = p) (ei : IsPrecompositionEquivalence i)
    (j : F ⟶ F') (hj : j ≫ q' = q) (ej : IsPrecompositionEquivalence j)
    (k : D ⟶ B) (h : IsQCatEquivalence (relativeFunctorPullback p' q' k)) :
    IsQCatEquivalence (relativeFunctorPullback p q k) := by
  have hi' := fiberComparisonBaseChange_isPrecompositionEquivalence p p' i hi ei k
  have hj' := fiberComparisonBaseChange_isPrecompositionEquivalence q q' j hj ej k
  have hpre := relativeFunctorOverPre_isQCatEquivalence q'
    (Over.homMk (U := Over.mk p) (V := Over.mk p') i hi) ei
  have hpre' := relativeFunctorOverPre_isQCatEquivalence (pullback.snd q' k)
    (Over.homMk (U := Over.mk (pullback.snd p k))
      (V := Over.mk (pullback.snd p' k)) (fiberComparisonBaseChange p p' i hi k)
      (fiberComparisonBaseChange_projection p p' i hi k)) hi'
  have hmiddle : IsQCatEquivalence (relativeFunctorPullback p q' k) := by
    apply hpre.cancel_left
    have hn := relativeFunctorPullback_pre q'
      (Over.homMk (U := Over.mk p) (V := Over.mk p') i hi) k
    exact hn.symm ▸ h.comp hpre'
  have hpost := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    q q' j hj ej p
  have hpost' := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    (pullback.snd q k) (pullback.snd q' k) (fiberComparisonBaseChange q q' j hj k)
    (fiberComparisonBaseChange_projection q q' j hj k) hj' (pullback.snd p k)
  apply hpost'.cancel_right
  rw [← relativeFunctorPullback_post]
  exact hpost.comp hmiddle

end SerrePositivity.InfinityCategories
