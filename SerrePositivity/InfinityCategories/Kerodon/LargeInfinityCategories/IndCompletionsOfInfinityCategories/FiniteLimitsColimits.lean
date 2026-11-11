module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteHornLimitsColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FiniteEndpoints

/-!
概要：Ind の全有限単体集合形状の極限・余極限存在を公開する。
方針：元の C の端点を Yoneda で送り、標準 span/cospan から一般有限生成する。
規約：正則 κ・明示交換入力・元の C の有限全存在を明示する。
使われ方：I-2 c の安定性。C の安定性からの有限全存在は D-7′ の供給に接続する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 明示交換入力と C の有限極限から、Ind の全有限極限が存在する。 -/
lemma ind_hasFiniteLimits (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := by
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.exists_terminal_of_hasFiniteLimits (X := C)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isTerminal_of_terminal κ ht)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_cospan_hasLimit κ hκ hex)

/-- 明示交換入力と C の有限余極限から、Ind の全有限余極限が存在する。 -/
lemma ind_hasFiniteColimits (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := by
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.exists_initial_of_hasFiniteColimits (X := C)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isInitial_of_initial κ hκ ht)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_span_hasColimit κ hκ hex)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
