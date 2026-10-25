module

public import SerrePositivity.InfinityCategories.F2.Ind.UnconditionalFiniteLimitsColimits
public import SerrePositivity.InfinityCategories.F2.Ind.StableSourceCompactGeneration

/-!
概要：安定 Ind・完全 Yoneda・compact 生成から有限交換の入力仮定を除く。
方針：証明済みの全有限交換を同じ元の安定性・生成界面へ代入する。
規約：元の全四角形と生成同値を保持し、既存宣言の型を変えない。
使われ方：I-2 d′、K-B の K-7 d4 向け最終公開界面。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 正則 κ と小さい安定 C から、交換の追加仮定なしに同じ Ind は安定。 -/
lemma ind_isStable_unconditional (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    IsStable (IndInfinity κ C) :=
  ind_isStable_of_isStable κ hκ indFiniteLimitExchangeInput C

/-- 同じ元の全四角形の引き戻し性と押し出し性は、交換の追加仮定なしに一致する。 -/
lemma ind_isPullbackSquare_iff_isPushoutSquare_unconditional
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{u}} [Quasicategory C] [IsStable C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ IndInfinity κ C) :
    IsPullbackSquare L ↔ IsPushoutSquare L :=
  ind_isPullbackSquare_iff_isPushoutSquare_of_isStable κ hκ indFiniteLimitExchangeInput L

/-- 同じ元の Yoneda は、安定 Ind への充満忠実な完全包含。 -/
lemma ind_stable_with_fullyFaithful_exactYoneda_unconditional
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 ≤ κ)
    (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    IsStable (IndInfinity κ C) ∧ IsFullyFaithful (indYoneda κ C) ∧
      IsExactFunctor (indYoneda κ C) :=
  ind_stable_with_fullyFaithful_exactYoneda_of_isStable κ hκ indFiniteLimitExchangeInput C

/-- 安定な冪等完備 C の、交換入力を要求しない同じ全 compact 生成界面。 -/
def ind_stableCompactGeneration_unconditional (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (hC : Idempotent.IsIdempotentComplete C) : StableCompactGeneration κ C :=
  ind_stableCompactGeneration_of_isStable κ hκ indFiniteLimitExchangeInput C hC

/-- 無条件の公開界面の生成同値は、元の同じ選択した同値そのもの。 -/
lemma ind_stableCompactGeneration_unconditional_equivalence
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 ≤ κ)
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (hC : Idempotent.IsIdempotentComplete C) :
    (ind_stableCompactGeneration_unconditional κ hκ C hC).equivalence =
      compactGenerationEquivalence κ hC := rfl

end SerrePositivity.InfinityCategories.F2.Ind
