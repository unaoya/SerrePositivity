module

public import SerrePositivity.InfinityCategories.F2.Ind.StableSourceFiniteLimitsColimits
public import SerrePositivity.InfinityCategories.F2.Ind.StableCompactGeneration

/-!
概要：安定な冪等完備 C について、有限全存在を追加仮定にしない compact 生成界面。
方針：D-7′ の有限全存在を局所設定し、元の生成同値を持つ公開界面に渡す。
規約：交換入力は明示のまま保ち、元の Yoneda・生成同値・全選択比較を保持する。
使われ方：I-2 e′、K-B の K-7 d4 向けの最終公開入口。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 安定な冪等完備 C の、元の安定 Ind と compact 生成の全公開界面。 -/
def ind_stableCompactGeneration_of_isStable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (hC : Idempotent.IsIdempotentComplete C) : StableCompactGeneration κ C := by
  letI : HasFiniteLimits C := hasFiniteLimits_of_isStable C
  letI : HasFiniteColimits C := hasFiniteColimits_of_isStable C
  exact ind_stableCompactGeneration κ hκ hex C hC

/-- 新しい公開界面でも、選んだ compact 生成同値そのものを厳密に保持する。 -/
lemma ind_stableCompactGeneration_of_isStable_equivalence
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (hC : Idempotent.IsIdempotentComplete C) :
    (ind_stableCompactGeneration_of_isStable κ hκ hex C hC).equivalence =
      compactGenerationEquivalence κ hC := rfl

/-- 同じ選択した逆射と元の Yoneda の合成は、全 compact 包含と同型。 -/
def ind_stableCompactGeneration_of_isStable_inverse_inclusion
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (hC : Idempotent.IsIdempotentComplete C) :
    FunctorIso ((ind_stableCompactGeneration_of_isStable κ hκ hex C hC).equivalence.inv ≫
      indYoneda κ C) (Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)) :=
  (ind_stableCompactGeneration_of_isStable κ hκ hex C hC).inverse_inclusion

end SerrePositivity.InfinityCategories.F2.Ind
