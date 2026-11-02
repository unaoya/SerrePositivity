module

public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackLift

/-!
概要：path 引き戻しの二入力射は、両端評価の引き戻しであり Kan fibration。
方針：元の三座標を保つ普遍性で一段の引き戻し表示を証明する。
規約：二入力の圏の Kan 性は不要、path の標的にだけ Kan 性を要求する。
使われ方：標的引き戻しの二入力を元の全空間へ同時に変形する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H : SSet.{u}} (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：元の二入力を組にする射。
方針：二つの指定射影。規約：左・右の順。使われ方：二入力の同時輸送。 -/
def intervalPullbackInputPair : intervalPullback f g ⟶ E ⊗ D :=
  lift (intervalPullbackLeft f g) (intervalPullbackRight f g)

/-- 概要：path 引き戻しは両端評価を元の二射で引き戻したもの。
方針：三座標の持ち上げと一意性。規約：指定全 path。使われ方：二入力射の充填性。 -/
lemma intervalPullbackInputPair_isPullback :
    IsPullback (intervalPullbackPath f g) (intervalPullbackInputPair f g)
      (arrowEndpointPair H) (lift (fst E D ≫ f) (snd E D ≫ g)) := by
  have hc : intervalPullbackPath f g ≫ arrowEndpointPair H =
      intervalPullbackInputPair f g ≫ lift (fst E D ≫ f) (snd E D ≫ g) := by
    apply CartesianMonoidalCategory.hom_ext
    · change intervalPullbackPath f g ≫ (intervalEndpointNatTrans 0).app H =
        lift (intervalPullbackLeft f g) (intervalPullbackRight f g) ≫ fst E D ≫ f
      rw [← Category.assoc, lift_fst, intervalPullbackPath_zero]
    · change intervalPullbackPath f g ≫ (intervalEndpointNatTrans 1).app H =
        lift (intervalPullbackLeft f g) (intervalPullbackRight f g) ≫ snd E D ≫ g
      rw [← Category.assoc, lift_snd, intervalPullbackPath_one]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc)
  apply PullbackCone.isLimitAux'
  intro s
  have h₀ : s.fst ≫ (intervalEndpointNatTrans 0).app H = (s.snd ≫ fst E D) ≫ f := by
    have h := congrArg (fun r ↦ r ≫ fst H H) s.condition
    simpa only [arrowEndpointPair, intervalEndpointNatTrans, Category.assoc, lift_fst] using h
  have h₁ : s.fst ≫ (intervalEndpointNatTrans 1).app H = (s.snd ≫ snd E D) ≫ g := by
    have h := congrArg (fun r ↦ r ≫ snd H H) s.condition
    simpa only [arrowEndpointPair, intervalEndpointNatTrans, Category.assoc, lift_snd] using h
  let a := intervalPullbackLift f g s.fst (s.snd ≫ fst E D) (s.snd ≫ snd E D) h₀ h₁
  refine ⟨a, intervalPullbackLift_path _ _ _ _ _ _ _, ?_, ?_⟩
  · change a ≫ intervalPullbackInputPair f g = s.snd
    apply CartesianMonoidalCategory.hom_ext
    · rw [intervalPullbackInputPair, Category.assoc, lift_fst]
      exact intervalPullbackLift_left _ _ _ _ _ _ _
    · rw [intervalPullbackInputPair, Category.assoc, lift_snd]
      exact intervalPullbackLift_right _ _ _ _ _ _ _
  · intro m hm ht
    change m ≫ intervalPullbackInputPair f g = s.snd at ht
    apply intervalPullback_hom_ext f g
    · rw [show a ≫ intervalPullbackPath f g = s.fst from
        intervalPullbackLift_path _ _ _ _ _ _ _]
      exact hm
    · rw [show a ≫ intervalPullbackLeft f g = s.snd ≫ fst E D from
        intervalPullbackLift_left _ _ _ _ _ _ _]
      have h := congrArg (fun r ↦ r ≫ fst E D) ht
      simpa only [intervalPullbackInputPair, Category.assoc, lift_fst] using h
    · rw [show a ≫ intervalPullbackRight f g = s.snd ≫ snd E D from
        intervalPullbackLift_right _ _ _ _ _ _ _]
      have h := congrArg (fun r ↦ r ≫ snd E D) ht
      simpa only [intervalPullbackInputPair, Category.assoc, lift_snd] using h

/-- 概要：Kan 標的の path 引き戻しからの二入力射は Kan fibration。
方針：両端評価の引き戻し表示で充填性を移す。
規約：元の二入力射そのもの。使われ方：指定 path の両端の同時変形。 -/
instance intervalPullbackInputPair_fibration [KanComplex H] :
    Fibration (intervalPullbackInputPair f g) := by
  rw [← (intervalPullbackInputPair_isPullback f g).isoPullback_hom_snd]
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  exact J.rlp.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    (J.rlp.pullback_snd _ _ ((SSet.modelCategoryQuillen.fibration_iff _).1
      (inferInstanceAs (Fibration (arrowEndpointPair H)))))

end SerrePositivity.InfinityCategories.F2
