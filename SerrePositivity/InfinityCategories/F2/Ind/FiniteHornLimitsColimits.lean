module

public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetLimits
public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetColimits
public import SerrePositivity.InfinityCategories.F1.Simplicial.FiniteHornUniverseIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite

/-!
概要：元の大きい宇宙の標準 span/cospan の Ind 図式の余極限・極限を構成する。
方針：小さい有限半順序 nerve の持ち上げへ厳密な形状同型で戻す。
規約：明示交換入力と元の C の有限全存在を保持する。
使われ方：Ind の全有限極限・余極限を一般生成定理で結論する基底。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の標準 span の Ind 図式は余極限を持つ。 -/
lemma ind_span_hasColimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [HasFiniteColimits C]
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ IndInfinity κ C) : HasColimit p := by
  apply (F1B.kanHasColimit_iff_restrict_of_isIso p
    (uliftFiniteSpanNerveIso.{u, u + 1}).hom).mpr
  exact indFinitePoset_hasColimit κ hκ hex _

/-- 元の標準 cospan の Ind 図式は極限を持つ。 -/
lemma ind_cospan_hasLimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [HasFiniteLimits C]
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ IndInfinity κ C) : HasLimit p := by
  apply (F1B.kanHasLimit_iff_restrict_of_isIso p
    (uliftFiniteCospanNerveIso.{u, u + 1}).hom).mpr
  exact indFinitePoset_hasLimit κ hκ hex _

end SerrePositivity.InfinityCategories.F2.Ind
