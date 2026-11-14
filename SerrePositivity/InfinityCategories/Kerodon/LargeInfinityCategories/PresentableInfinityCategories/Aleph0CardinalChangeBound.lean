module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeBound

/-!
概要：非可算濃度は ℵ₀ からの濃度変更の冪評価を満たす。
方針：有限冪を底と ℵ₀ の最大値で抑える。
規約：この評価自体に正則性は要求しない。
使われ方：非可算正則濃度の小さい余極限の compact 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：ℵ₀ より大きい任意の濃度は ℵ₀ からの濃度変更条件を満たす。
方針：指数を自然数に戻し、有限冪を max β ℵ₀ 以下に抑える。
規約：κ の正則性をこの補題の仮定に含めない。
使われ方：非可算正則 κ の poset 余極限の compact 閉性。 -/
lemma cardinalChangeBound_aleph0 {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound Cardinal.aleph0 κ := by
  refine ⟨hκ, fun α β hα hβ ↦ ?_⟩
  lift α to ℕ using hα
  exact Cardinal.power_nat_le_max.trans_lt (max_lt hβ hκ)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.5.12"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalChangeBound_aleph0
