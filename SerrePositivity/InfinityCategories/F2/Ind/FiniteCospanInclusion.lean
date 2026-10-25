module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteHornLimitsColimits

/-!
概要：元の標準 cospan の指定極限錐を、Ind の前層への包含が保存・反映する。
方針：有限半順序 nerve の形状同型で制限し、同じ全錐を往復する。
規約：正則 κ・明示交換入力・C の有限極限存在を保持する。
使われ方：I-2 c の元の fiber 四角形と点ごとの filtered 補完の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の標準 cospan の任意の指定極限全錐を包含が保存する。 -/
lemma ind_cospan_inclusion_isLimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [HasFiniteLimits C]
    {p : (horn 2 2 : SSet.{u + 1}) ⟶ IndInfinity κ C}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c) := by
  let e := (uliftFiniteCospanNerveIso.{u, u + 1}).hom
  have hr := (F2.isLimitCone_restrict_iff_of_isIso c e).mpr hc
  have hi := indFinitePoset_inclusion_isLimit κ hκ hex (e ≫ p)
    (restrictJoinCone c e) hr
  apply (F2.isLimitCone_restrict_iff_of_isIso
    (mapJoinCone (indInclusionPresheaf κ C) c) e).mp
  apply (F2.isLimitCone_iff_of_cone_val_eq _ _ (Category.assoc _ _ _)).mp hi

/-- 元の標準 cospan の指定全錐の極限性は包含によって保存・反映される。 -/
lemma ind_cospan_isLimit_iff_inclusion (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [HasFiniteLimits C]
    {p : (horn 2 2 : SSet.{u + 1}) ⟶ IndInfinity κ C} (c : JoinCone p) :
    IsLimitCone c ↔ IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c) :=
  ⟨ind_cospan_inclusion_isLimit κ hκ hex c, ind_isLimit_of_inclusion κ p c⟩

/-- 包含は同じ実引き戻し四角形を保存する。 -/
lemma ind_inclusion_preservesPullbackSquare (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [HasFiniteLimits C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ IndInfinity κ C)
    (hL : IsPullbackSquare L) :
    IsPullbackSquare (L ≫ indInclusionPresheaf κ C) := by
  have h := ind_cospan_inclusion_isLimit κ hκ hex (pullbackCone L) hL
  exact (F2.isLimitCone_iff_of_cone_val_eq _ _ (Category.assoc _ _ _)).mp h

/-- 同じ実四角形の引き戻し性は包含によって保存・反映される。 -/
lemma ind_inclusion_isPullbackSquare_iff (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [HasFiniteLimits C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ IndInfinity κ C) :
    IsPullbackSquare L ↔ IsPullbackSquare (L ≫ indInclusionPresheaf κ C) := by
  refine ⟨ind_inclusion_preservesPullbackSquare κ hκ hex L, fun h => ?_⟩
  apply ind_isLimit_of_inclusion κ _ (pullbackCone L)
  exact (F2.isLimitCone_iff_of_cone_val_eq _ _ (Category.assoc _ _ _)).mpr h

end SerrePositivity.InfinityCategories.F2.Ind
