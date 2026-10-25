module

public import SerrePositivity.InfinityCategories.F2.Ind.Stability
public import SerrePositivity.InfinityCategories.Stable.StableFiniteLimitsColimits

/-!
概要：安定な C から、Ind の有限全存在と安定性を明示交換入力のもとで導く。
方針：D-7′ の有限全存在を証明内の局所 instance に置き、保存済みの結論に渡す。
規約：C の有限全存在を追加仮定にせず、既存宣言と交換入力を変更しない。
使われ方：I-2 e′、K-B の K-7 d4 における安定 Ind と完全 Yoneda。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 安定な C の Ind は、明示交換入力のもとで全有限極限を持つ。 -/
lemma ind_hasFiniteLimits_of_isStable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    HasFiniteLimits (IndInfinity κ C) := by
  let : HasFiniteLimits C := hasFiniteLimits_of_isStable C
  exact ind_hasFiniteLimits κ hκ hex C

/-- 安定な C の Ind は、明示交換入力のもとで全有限余極限を持つ。 -/
lemma ind_hasFiniteColimits_of_isStable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    HasFiniteColimits (IndInfinity κ C) := by
  let : HasFiniteColimits C := hasFiniteColimits_of_isStable C
  exact ind_hasFiniteColimits κ hκ hex C

/-- 元の C の安定性だけから、明示交換入力のもとで同じ Ind の安定性を導く。 -/
lemma ind_isStable_of_isStable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C] : IsStable (IndInfinity κ C) := by
  let : HasFiniteLimits C := hasFiniteLimits_of_isStable C
  let : HasFiniteColimits C := hasFiniteColimits_of_isStable C
  exact ind_isStable κ hκ hex C

/-- C の有限全存在を仮定せず、元の実四角形の fiber/cofiber 判定を与える。 -/
lemma ind_isPullbackSquare_iff_isPushoutSquare_of_isStable
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ IndInfinity κ C) :
    IsPullbackSquare L ↔ IsPushoutSquare L := by
  let : HasFiniteLimits C := hasFiniteLimits_of_isStable C
  let : HasFiniteColimits C := hasFiniteColimits_of_isStable C
  exact ind_isPullbackSquare_iff_isPushoutSquare κ hκ hex L

/-- 安定な C の同じ元の Yoneda は、安定 Ind への充満忠実な完全包含。 -/
lemma ind_stable_with_fullyFaithful_exactYoneda_of_isStable
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    IsStable (IndInfinity κ C) ∧ IsFullyFaithful (indYoneda κ C) ∧
      IsExactFunctor (indYoneda κ C) := by
  let : HasFiniteLimits C := hasFiniteLimits_of_isStable C
  let : HasFiniteColimits C := hasFiniteColimits_of_isStable C
  exact ind_stable_with_fullyFaithful_exactYoneda κ hκ hex C

end SerrePositivity.InfinityCategories.F2.Ind
