module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConePresheafRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteLimitExchangeInput
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.VertexConeIsoTransport

/-!
概要：Indκ の全前層は、交換定理を入力した形状の元の極限全錐を保存する。
方針：表現可能前層の保存性を、全錐の制限族の同型と κ-filtered 閉包へ移す。
規約：交換定理は明示引数。この定理でその入力の存在を主張しない。
使われ方：Ind の表現可能な有限余極限錐の普遍性と、安定性への条件付き経路。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 全錐を保つ一般 coherent 交換から、最小 κ-filtered 閉包の全頂点での極限性を得る。 -/
lemma indVertex_cone_isLimit_of_exchange (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchangeShape K)
    {v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction c).app (Opposite.op ⦋0⦌) v)) := by
  apply hv (fun w => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction c).app (Opposite.op ⦋0⦌) w)))
  · intro y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction_isLimit_iff c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_isLimit c hc y)
  · intro a b e ha
    exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_functorVertexCone_iff_of_vertexIso
      (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction c))).mp ha
  · intro I hI hFiltered p d hd hp
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hκ I
    have ht := hK I (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction c) d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction_isPointwiseColimit c p d hd) hp
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex] at ht
    exact ht

/-- 明示の有限交換入力から、元の Ind 前層による同じ有限全錐の極限保存を得る。 -/
lemma indPresheaf_finiteCone_isLimit (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] {D : K ⟶ C.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.conePresheafRestriction_isLimit_iff c F).mp
    (indVertex_cone_isLimit_of_exchange κ hκ c hc (hex.exchange K) hF)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
