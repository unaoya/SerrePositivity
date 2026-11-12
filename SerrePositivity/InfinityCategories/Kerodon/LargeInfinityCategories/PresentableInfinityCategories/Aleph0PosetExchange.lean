module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CardinalExchangeShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Aleph0CardinalChangeBound

/-!
概要：非可算正則 κ に対する小さい poset の全錐交換を同じ κ のまま公開する。
方針：P の poset 交換を κ′ = ℵ₀ の cardinalChangeBound で特殊化する。
規約：添字の濃度を拡大せず、指定された点ごとの余極限余錐を保持する。
使われ方：P-12 の小さい極限表示と κ-filtered 余極限の交換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：κ-small な poset の全極限錐は κ-filtered な点ごとの余極限で保たれる。
方針：P の全錐交換に cardinalChangeBound_aleph0 を適用する。
規約：下側濃度は ℵ₀、保存する濃度は元の κ。
使われ方：P-12 の end の極限錐の保存判定。 -/
lemma cardinalFilteredLimitExchangeShape_aleph0_poset
    {κ : Cardinal.{u}} [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (I : Type u) [PartialOrder I] (hI : HasCardinalLT I κ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CardinalFilteredLimitExchangeShape κ (nerve I) := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.cardinalFilteredLimitExchangeShape_poset (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalChangeBound_aleph0 hκ) I hI

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
