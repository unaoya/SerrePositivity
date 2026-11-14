module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SmallJoinCover
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SmallSubcomplexCovers

/-!
概要：正則 κ に対して κ-small な単体集合どうしの join は κ-small。
方針：非退化単体とその対で添字付けた有限部分複体の被覆を使う。
規約：κ = ℵ₀ も同じ証明に含む。
使われ方：κ-filtered ∞ 圏の κ-small な図式の下の coslice。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：小さい join の有限な部品の添字は κ 個未満である。
方針：非退化単体の型の和と積の濃度を評価する。
規約：この評価自体に正則性は不要。使われ方：被覆の小ささ。 -/
lemma smallJoinPiece_index_small {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {K L : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L) :
    Cardinal.mk (K.N ⊕ L.N ⊕ (K.N × L.N)) < κ := by
  simp only [Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.lift_id]
  exact Cardinal.add_lt_of_lt hκ hK
    (Cardinal.add_lt_of_lt hκ hL (Cardinal.mul_lt_of_lt hκ hK hL))

/-- 概要：正則 κ について κ-small な両因子の join は κ-small。
方針：κ 個未満の有限な部品による被覆に正則濃度の和の評価を使う。
規約：全ての非退化単体を数える。使われ方：κ-small な図式の結合。 -/
lemma isKappaSmall_join {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K L : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isKappaSmall_of_cover hκ (smallJoinPiece_index_small hκ.aleph0_le hK hL)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.smallJoinPiece K L) (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.iSup_smallJoinPiece K L)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
