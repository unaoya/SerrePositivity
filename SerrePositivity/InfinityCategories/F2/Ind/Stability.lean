module

public import SerrePositivity.InfinityCategories.F2.Ind.PullbacksArePushouts
public import SerrePositivity.InfinityCategories.F2.Ind.PushoutsArePullbacks
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaExactFunctor

/-!
概要：明示有限交換入力のもとで、安定な小さい圏の Ind の安定性を結論する。
方針：元の全四角形の双方向の普遍性、有限全存在、同じ Yoneda 零対象を結ぶ。
規約：C の有限極限・有限余極限は D-7′ の供給まで明示し、模型圏仮定を加えない。
使われ方：I-2 c の公開界面、compact 生成と K-B 向けの安定 Ind。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ元の Ind 全四角形について、引き戻し性と押し出し性が一致する。 -/
lemma ind_isPullbackSquare_iff_isPushoutSquare (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [IsStable C]
    [HasFiniteLimits C] [HasFiniteColimits C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ IndInfinity κ C) :
    IsPullbackSquare L ↔ IsPushoutSquare L :=
  ⟨ind_pushout_of_pullback_square κ hκ hex L, ind_pullback_of_pushout_square κ hκ hex L⟩

/-- 小さい安定圏の Ind は、明示有限交換と元の有限全存在のもとで安定である。 -/
lemma ind_isStable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    [HasFiniteLimits C] [HasFiniteColimits C] : IsStable (IndInfinity κ C) := by
  letI : HasZeroVertex (IndInfinity κ C) := ind_hasZeroVertex κ hκ C
  letI : HasFiniteLimits (IndInfinity κ C) := ind_hasFiniteLimits κ hκ hex C
  letI : HasFiniteColimits (IndInfinity κ C) := ind_hasFiniteColimits κ hκ hex C
  exact isStable_of_finite_limits_colimits (ind_isPullbackSquare_iff_isPushoutSquare κ hκ hex)

/-- 同じ元の Yoneda は、安定な Ind への充満忠実な完全包含である。 -/
lemma ind_stable_with_fullyFaithful_exactYoneda (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    [HasFiniteLimits C] [HasFiniteColimits C] :
    IsStable (IndInfinity κ C) ∧ IsFullyFaithful (indYoneda κ C) ∧
      IsExactFunctor (indYoneda κ C) :=
  ⟨ind_isStable κ hκ hex C, indYoneda_isFullyFaithful κ C, indYoneda_isExactFunctor κ hκ hex C⟩

end SerrePositivity.InfinityCategories.F2.Ind
