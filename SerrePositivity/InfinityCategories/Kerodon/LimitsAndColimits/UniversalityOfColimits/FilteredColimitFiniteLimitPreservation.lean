module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteLimitPreservationGeneration
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ChosenColimitExchange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LimitPreservationShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteExchangeBasicShapes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteExchangeUniverseShapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceLimitShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorFiniteLimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRepresentableLimits

/-!
概要：選択した元の filtered 空間値余極限関手は、全有限単体集合形状の極限を保つ。
方針：空形状と cospan の全錐交換を同じ関手の保存へ移し、有限セルで帰納する。
規約：D の有限存在 API をこの一葉からのみ import し、交換の入力仮定を置かない。
使われ方：I-2 d′ の一般 coherent 有限極限交換と Ind 入力の定理化。

対応節は Kerodon 7.7（Tag 05SB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits


/-- 小さい元の空間値図式の、全普遍余錐族から選ぶ余極限関手。 -/
def smallSpaceColimitFunctor (B : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor _ _ (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram p)

/-- 一般 filtered ∞ 添字の元の余極限関手は、任意の有限形状の指定全極限錐を保つ。 -/
lemma smallSpaceFilteredColimit_map_isLimit_finite
    (B : SSet.{u}) [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    {K : SSet.{u + 1}} [K.Finite]
    {p : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (smallSpaceColimitFunctor B) c) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionSpace_hasFiniteLimits
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_finite_of_empty_pointCospan (smallSpaceColimitFunctor B) ?_ ?_ c hc
  · intro T p d hd
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_of_shapeIso (smallSpaceColimitFunctor B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteExchangeEmptyLiftIso T)
      (fun q a ha ↦ ?_) d hd
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.chosenColimit_map_isLimit_of_exchange
      (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram p) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hasSpaceLimitsOfShape _)
      (by
        intro F c hc hF
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coherentFilteredLimitExchangeShape_empty (Δ[0] : SSet.{u}) B F c hc
          (fun b ↦ hF (ULift.up b))) a ha
  · intro p d hd
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_of_shapeIso (smallSpaceColimitFunctor B) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteExchangePointCospanLiftIso
      (fun q a ha ↦ ?_) d hd
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.chosenColimit_map_isLimit_of_exchange
      (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram p) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hasSpaceLimitsOfShape _)
      (by
        intro F c hc hF
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coherentFilteredLimitExchangeShape_cospanHorn B F c hc
          (fun b ↦ hF (ULift.up b))) a ha

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.UniversalityOfColimits
