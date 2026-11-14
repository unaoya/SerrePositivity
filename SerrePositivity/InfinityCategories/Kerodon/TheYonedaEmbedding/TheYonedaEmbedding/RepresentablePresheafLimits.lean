module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SpacePointLimitDetection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.SpaceLimitShapes

/-!
概要：元の表現可能前層による全極限錐の保存を、像の極限の存在から証明する。
方針：coslice の切断比較を元の native 全錐へ移し、一点からの切断で極限性を検出する。
規約：有限形状に限定しない。像の極限の存在は明示し、一般の小極限の存在と区別する。
使われ方：F1-4、HTT 5.1.3.2 の表現可能関手の極限保存。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) (y : C _⦋0⦌)

/-- 元の表現可能前層の像に極限があれば、同じ全極限錐そのものを保存する。 -/
lemma representablePresheafInfinity_isLimit_of_hasLimit (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit ((SSet.uliftFunctor.{u + 1, u}).map D ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.spaceCone_isLimit_of_pointRestriction_of_hasLimit _ hD
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableNativeConePointedRestriction_isQCatEquivalence c hc y)

/-- 元の形状の空間値極限が存在すれば、表現可能前層は全極限錐を保存する。 -/
lemma representablePresheafInfinity_isLimit_of_spaceLimitsOfShape (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hK : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.HasSpaceLimitsOfShape K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) :=
  representablePresheafInfinity_isLimit_of_hasLimit c y hc (hK _)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
