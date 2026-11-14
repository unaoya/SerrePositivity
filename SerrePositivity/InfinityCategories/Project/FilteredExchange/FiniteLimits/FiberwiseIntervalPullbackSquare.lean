module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalEndpointPair
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackInputPair

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の path 引き戻しは、fiber ごとの両端評価の元の二射に沿う引き戻し。
方針：両端条件から元の二段の持ち上げを構成し、三座標で一意性を示す。
規約：追加の充填性は不要。使われ方：両端を保持する相対持ち上げの輸送。 -/
lemma fiberwiseIntervalPullback_isPullback {E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair p) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseCospanPair p f g) := by
  have hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair p =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseCospanPair p f g := by
    apply pullback.hom_ext (f := p) (g := p)
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair, pullback.lift_fst,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseCospanPair_fst, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_fst, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath_zero]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair, pullback.lift_snd,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseCospanPair_snd, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_snd, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath_one]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc)
  apply PullbackCone.isLimitAux'
  intro s
  have h₀ : s.fst ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0 =
      (s.snd ≫ pullback.fst (f ≫ p) (g ≫ p)) ≫ f := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst p p) s.condition
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair, pullback.lift_fst,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseCospanPair_fst] using h
  have h₁ : s.fst ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1 =
      (s.snd ≫ pullback.snd (f ≫ p) (g ≫ p)) ≫ g := by
    have h := congrArg (fun z ↦ z ≫ pullback.snd p p) s.condition
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair, pullback.lift_snd,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseCospanPair_snd] using h
  let a := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift p f g s.fst
    (s.snd ≫ pullback.fst (f ≫ p) (g ≫ p)) (s.snd ≫ pullback.snd (f ≫ p) (g ≫ p)) h₀ h₁
  refine ⟨a, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift_path _ _ _ _ _ _ _ _, ?_, ?_⟩
  · change a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g = s.snd
    apply pullback.hom_ext (f := f ≫ p) (g := g ≫ p)
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_fst]
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift_left _ _ _ _ _ _ _ _
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_snd]
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift_right _ _ _ _ _ _ _ _
  · intro m hm ht
    change m ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g = s.snd at ht
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback_hom_ext p f g
    · rw [show a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g = s.fst from
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift_path _ _ _ _ _ _ _ _]
      exact hm
    · rw [show a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g =
        s.snd ≫ pullback.fst (f ≫ p) (g ≫ p) from
          _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift_left _ _ _ _ _ _ _ _]
      have h := congrArg (fun z ↦ z ≫ pullback.fst (f ≫ p) (g ≫ p)) ht
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_fst] using h
    · rw [show a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g =
        s.snd ≫ pullback.snd (f ≫ p) (g ≫ p) from
          _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLift_right _ _ _ _ _ _ _ _]
      have h := congrArg (fun z ↦ z ≫ pullback.snd (f ≫ p) (g ≫ p)) ht
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_snd] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
