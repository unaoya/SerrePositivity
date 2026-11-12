module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.FilteredColimitFiniteLimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteUniverse

/-!
概要：一般 coherent filtered 余極限と全有限単体集合形状の極限の交換を結論する。
方針：有限生成で証明した同じ余極限関手の保存を、元の指定全錐族へ戻す。
規約：一般交換を仮定せず、元の全図式と指定余極限を保持する。
使われ方：I-2 d′、Ind の有限全存在・安定性、compact 対象の有限余極限閉性。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories


/-- 任意の有限 K の元の全極限錐は、一般 coherent filtered 余極限で極限性を保つ。 -/
theorem coherentFilteredLimitExchangeShape_finite (K : SSet.{u}) [K.Finite] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchangeShape K := by
  intro B hB hFiltered F c hc hF
  have : ((SSet.uliftFunctor.{u + 1, u}).obj K).Finite :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finite_ulift_iff K).mpr inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneFamilyLimitExchange_of_chosenColimit_preservesLimits
    (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram p)
    (fun p a ha ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits.smallSpaceFilteredColimit_map_isLimit_finite B a ha) F c hc
    (fun b ↦ hF b.down)

/-- 全有限単体集合形状の交換入力を、証明済み定理から構成する。 -/
theorem indFiniteLimitExchangeInput : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u} where
  exchange K := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredLimitExchangeShape_finite K

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
