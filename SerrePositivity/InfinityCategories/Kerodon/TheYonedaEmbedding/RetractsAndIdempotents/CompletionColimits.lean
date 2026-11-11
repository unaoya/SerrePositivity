module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeReversePostcomp

/-!
概要：元の任意の冪等完備化は、元の図式に既に存在する全余極限余錐を保存する。
方針：元の全余錐を反転し、同じ元の反転関手の極限保存を適用する。
規約：有限性も inner 仮定も課さず、指定された元の余錐の像を保持する。
使われ方：HA 1.1.3.7 の既存の有限余極限と cofiber 四角形の移送。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の任意の冪等完備化は、元の全図式の指定余極限余錐の同じ像を余極限へ送る。 -/
lemma IsIdempotentCompletion.mapJoinCocone_isColimit {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    {p : K ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone f c) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.mapJoinCone_isLimit (SSet.opFunctor.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op_general f hf) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone c).mp hc)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_reverse_postcomp_iff c f).mp h

/-- 元の任意の冪等完備化は、元の図式の余極限の存在をその同じ像へ移す。 -/
lemma IsIdempotentCompletion.hasColimit_comp {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (p : K ⟶ C) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (p ≫ f) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone f c, IsIdempotentCompletion.mapJoinCocone_isColimit f hf c hc⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
