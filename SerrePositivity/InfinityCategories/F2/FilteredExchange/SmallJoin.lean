module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallSubcomplexCovers
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallJoinCover

/-!
概要：正則 κ に対して κ-small な単体集合どうしの join は κ-small。
方針：非退化単体とその対で添字付けた有限部分複体の被覆を使う。
規約：κ = ℵ₀ も同じ証明に含む。
使われ方：κ-filtered ∞ 圏の κ-small な図式の下の coslice。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：小さい join の有限な部品の添字は κ 個未満である。
方針：非退化単体の型の和と積の濃度を評価する。
規約：この評価自体に正則性は不要。使われ方：被覆の小ささ。 -/
lemma smallJoinPiece_index_small {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {K L : SSet.{u}} (hK : IsKappaSmall κ K) (hL : IsKappaSmall κ L) :
    Cardinal.mk (K.N ⊕ L.N ⊕ (K.N × L.N)) < κ := by
  simp only [Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.lift_id]
  exact Cardinal.add_lt_of_lt hκ hK
    (Cardinal.add_lt_of_lt hκ hL (Cardinal.mul_lt_of_lt hκ hK hL))

/-- 概要：正則 κ について κ-small な両因子の join は κ-small。
方針：κ 個未満の有限な部品による被覆に正則濃度の和の評価を使う。
規約：全ての非退化単体を数える。使われ方：κ-small な図式の結合。 -/
lemma isKappaSmall_join {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K L : SSet.{u}} (hK : IsKappaSmall κ K) (hL : IsKappaSmall κ L) :
    IsKappaSmall κ (join K L) :=
  isKappaSmall_of_cover hκ (smallJoinPiece_index_small hκ.aleph0_le hK hL)
    (smallJoinPiece K L) (fun _ ↦ isKappaSmall_of_finite hκ.aleph0_le _)
    (iSup_smallJoinPiece K L)

end SerrePositivity.InfinityCategories.F2
