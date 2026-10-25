module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteHornLimitsColimits
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaZero
public import SerrePositivity.InfinityCategories.F1.Joins.FiniteEndpoints

/-!
概要：Ind の全有限単体集合形状の極限・余極限存在を公開する。
方針：元の C の端点を Yoneda で送り、標準 span/cospan から一般有限生成する。
規約：正則 κ・明示交換入力・元の C の有限全存在を明示する。
使われ方：I-2 c の安定性。C の安定性からの有限全存在は D-7′ の供給に接続する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 明示交換入力と C の有限極限から、Ind の全有限極限が存在する。 -/
lemma ind_hasFiniteLimits (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [HasFiniteLimits C] :
    HasFiniteLimits (IndInfinity κ C) := by
  obtain ⟨t, ht⟩ := exists_terminal_of_hasFiniteLimits (X := C)
  exact hasFiniteLimits_of_terminal_pullbacks _ (indYoneda_isTerminal_of_terminal κ ht)
    (ind_cospan_hasLimit κ hκ hex)

/-- 明示交換入力と C の有限余極限から、Ind の全有限余極限が存在する。 -/
lemma ind_hasFiniteColimits (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [HasFiniteColimits C] :
    HasFiniteColimits (IndInfinity κ C) := by
  obtain ⟨t, ht⟩ := exists_initial_of_hasFiniteColimits (X := C)
  exact hasFiniteColimits_of_initial_pushouts _ (indYoneda_isInitial_of_initial κ hκ ht)
    (ind_span_hasColimit κ hκ hex)

end SerrePositivity.InfinityCategories.F2.Ind
