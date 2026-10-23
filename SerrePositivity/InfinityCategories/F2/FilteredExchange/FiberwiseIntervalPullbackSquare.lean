module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseIntervalEndpointPair
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackInputPair
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwiseIntervalPullbackLift

/-!
概要：二段の fiber ごとの path 引き戻しは、相対両端評価の一段の引き戻し。
方針：元の三座標を保つ持ち上げと一意性で厳密な引き戻しを証明する。
規約：元の二入力と底を固定した全 path を保持する。
使われ方：両端を固定した相対持ち上げ性と有限検出の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の path 引き戻しは、fiber ごとの両端評価の元の二射に沿う引き戻し。
方針：両端条件から元の二段の持ち上げを構成し、三座標で一意性を示す。
規約：追加の充填性は不要。使われ方：両端を保持する相対持ち上げの輸送。 -/
lemma fiberwiseIntervalPullback_isPullback {E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) :
    IsPullback (fiberwiseIntervalPullbackPath p f g) (fiberwisePullbackInputPair p f g)
      (fiberwiseIntervalEndpointPair p) (fiberwiseCospanPair p f g) := by
  have hc : fiberwiseIntervalPullbackPath p f g ≫ fiberwiseIntervalEndpointPair p =
      fiberwisePullbackInputPair p f g ≫ fiberwiseCospanPair p f g := by
    apply pullback.hom_ext (f := p) (g := p)
    · rw [Category.assoc, fiberwiseIntervalEndpointPair, pullback.lift_fst,
        Category.assoc, fiberwiseCospanPair_fst, ← Category.assoc,
        fiberwisePullbackInputPair_fst, fiberwiseIntervalPullbackPath_zero]
    · rw [Category.assoc, fiberwiseIntervalEndpointPair, pullback.lift_snd,
        Category.assoc, fiberwiseCospanPair_snd, ← Category.assoc,
        fiberwisePullbackInputPair_snd, fiberwiseIntervalPullbackPath_one]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc)
  apply PullbackCone.isLimitAux'
  intro s
  have h₀ : s.fst ≫ fiberwiseIntervalEndpoint p 0 =
      (s.snd ≫ pullback.fst (f ≫ p) (g ≫ p)) ≫ f := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst p p) s.condition
    simpa only [Category.assoc, fiberwiseIntervalEndpointPair, pullback.lift_fst,
      fiberwiseCospanPair_fst] using h
  have h₁ : s.fst ≫ fiberwiseIntervalEndpoint p 1 =
      (s.snd ≫ pullback.snd (f ≫ p) (g ≫ p)) ≫ g := by
    have h := congrArg (fun z ↦ z ≫ pullback.snd p p) s.condition
    simpa only [Category.assoc, fiberwiseIntervalEndpointPair, pullback.lift_snd,
      fiberwiseCospanPair_snd] using h
  let a := fiberwiseIntervalPullbackLift p f g s.fst
    (s.snd ≫ pullback.fst (f ≫ p) (g ≫ p)) (s.snd ≫ pullback.snd (f ≫ p) (g ≫ p)) h₀ h₁
  refine ⟨a, fiberwiseIntervalPullbackLift_path _ _ _ _ _ _ _ _, ?_, ?_⟩
  · change a ≫ fiberwisePullbackInputPair p f g = s.snd
    apply pullback.hom_ext (f := f ≫ p) (g := g ≫ p)
    · rw [Category.assoc, fiberwisePullbackInputPair_fst]
      exact fiberwiseIntervalPullbackLift_left _ _ _ _ _ _ _ _
    · rw [Category.assoc, fiberwisePullbackInputPair_snd]
      exact fiberwiseIntervalPullbackLift_right _ _ _ _ _ _ _ _
  · intro m hm ht
    change m ≫ fiberwisePullbackInputPair p f g = s.snd at ht
    apply fiberwiseIntervalPullback_hom_ext p f g
    · rw [show a ≫ fiberwiseIntervalPullbackPath p f g = s.fst from
        fiberwiseIntervalPullbackLift_path _ _ _ _ _ _ _ _]
      exact hm
    · rw [show a ≫ fiberwiseIntervalPullbackLeft p f g =
        s.snd ≫ pullback.fst (f ≫ p) (g ≫ p) from
          fiberwiseIntervalPullbackLift_left _ _ _ _ _ _ _ _]
      have h := congrArg (fun z ↦ z ≫ pullback.fst (f ≫ p) (g ≫ p)) ht
      simpa only [Category.assoc, fiberwisePullbackInputPair_fst] using h
    · rw [show a ≫ fiberwiseIntervalPullbackRight p f g =
        s.snd ≫ pullback.snd (f ≫ p) (g ≫ p) from
          fiberwiseIntervalPullbackLift_right _ _ _ _ _ _ _ _]
      have h := congrArg (fun z ↦ z ≫ pullback.snd (f ≫ p) (g ≫ p)) ht
      simpa only [Category.assoc, fiberwisePullbackInputPair_snd] using h

end SerrePositivity.InfinityCategories.F2
