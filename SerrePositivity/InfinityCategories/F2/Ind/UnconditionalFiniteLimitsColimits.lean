module

public import SerrePositivity.InfinityCategories.F2.Ind.CoherentFiniteLimitExchange
public import SerrePositivity.InfinityCategories.F2.Ind.StableSourceFiniteLimitsColimits

/-!
概要：証明済みの有限交換を代入し、Ind の有限全存在から交換入力を除く。
方針：元の C の有限全存在を使う一般形と、安定性から導く系を既存界面へ接続する。
規約：既存宣言を変更せず、交換や模型圏の instance を追加しない。
使われ方：I-2 d′ の公開結論、安定 Ind と compact 生成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 正則 κ と元の C の有限極限だけから、同じ Ind の全有限極限が存在する。 -/
lemma ind_hasFiniteLimits_unconditional (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (C : SSet.{u}) [Quasicategory C] [HasFiniteLimits C] :
    HasFiniteLimits (IndInfinity κ C) :=
  ind_hasFiniteLimits κ hκ indFiniteLimitExchangeInput C

/-- 正則 κ と元の C の有限余極限だけから、同じ Ind の全有限余極限が存在する。 -/
lemma ind_hasFiniteColimits_unconditional (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (C : SSet.{u}) [Quasicategory C] [HasFiniteColimits C] :
    HasFiniteColimits (IndInfinity κ C) :=
  ind_hasFiniteColimits κ hκ indFiniteLimitExchangeInput C

/-- 安定な C の Ind は、交換入力や C の有限全存在の追加仮定なしに全有限極限を持つ。 -/
lemma ind_hasFiniteLimits_of_isStable_unconditional
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 ≤ κ)
    (C : SSet.{u}) [Quasicategory C] [IsStable C] : HasFiniteLimits (IndInfinity κ C) :=
  ind_hasFiniteLimits_of_isStable κ hκ indFiniteLimitExchangeInput C

/-- 安定な C の Ind は、交換入力や C の有限全存在の追加仮定なしに全有限余極限を持つ。 -/
lemma ind_hasFiniteColimits_of_isStable_unconditional
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 ≤ κ)
    (C : SSet.{u}) [Quasicategory C] [IsStable C] : HasFiniteColimits (IndInfinity κ C) :=
  ind_hasFiniteColimits_of_isStable κ hκ indFiniteLimitExchangeInput C

end SerrePositivity.InfinityCategories.F2.Ind
