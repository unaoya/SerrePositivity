module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FinitePosetLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FinitePosetColimits
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteHornUniverseIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite

/-!
概要：元の大きい宇宙の標準 span/cospan の Ind 図式の余極限・極限を構成する。
方針：小さい有限半順序 nerve の持ち上げへ厳密な形状同型で戻す。
規約：明示交換入力と元の C の有限全存在を保持する。
使われ方：Ind の全有限極限・余極限を一般生成定理で結論する基底。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の標準 span の Ind 図式は余極限を持つ。 -/
lemma ind_span_hasColimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C]
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso p
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.uliftFiniteSpanNerveIso.{u, u + 1}).hom).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indFinitePoset_hasColimit κ hκ hex _

/-- 元の標準 cospan の Ind 図式は極限を持つ。 -/
lemma ind_cospan_hasLimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C]
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_restrict_of_isIso p
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.uliftFiniteCospanNerveIso.{u, u + 1}).hom).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indFinitePoset_hasLimit κ hκ hex _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
