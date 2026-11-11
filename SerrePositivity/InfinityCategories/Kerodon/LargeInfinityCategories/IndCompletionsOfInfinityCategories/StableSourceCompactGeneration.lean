module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StableSourceFiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StableCompactGeneration

/-!
概要：安定な冪等完備 C について、有限全存在を追加仮定にしない compact 生成界面。
方針：D-7′ の有限全存在を局所設定し、元の生成同値を持つ公開界面に渡す。
規約：交換入力は明示のまま保ち、元の Yoneda・生成同値・全選択比較を保持する。
使われ方：I-2 e′、K-B の K-7 d4 向けの最終公開入口。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 安定な冪等完備 C の、元の安定 Ind と compact 生成の全公開界面。 -/
def ind_stableCompactGeneration_of_isStable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StableCompactGeneration κ C := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable C
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteColimits_of_isStable C
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_stableCompactGeneration κ hκ hex C hC

/-- 新しい公開界面でも、選んだ compact 生成同値そのものを厳密に保持する。 -/
lemma ind_stableCompactGeneration_of_isStable_equivalence
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) :
    (ind_stableCompactGeneration_of_isStable κ hκ hex C hC).equivalence =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence κ hC := rfl

/-- 同じ選択した逆射と元の Yoneda の合成は、全 compact 包含と同型。 -/
def ind_stableCompactGeneration_of_isStable_inverse_inclusion
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((ind_stableCompactGeneration_of_isStable κ hκ hex C hC).equivalence.inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)) :=
  (ind_stableCompactGeneration_of_isStable κ hκ hex C hC).inverse_inclusion

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
