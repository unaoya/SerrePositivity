module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitPreservationGeneration
public import SerrePositivity.InfinityCategories.F2.Ind.ChosenColimitExchange
public import SerrePositivity.InfinityCategories.F2.Ind.LimitPreservationShapeIso
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteExchangeBasicShapes
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteExchangeUniverseShapes
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.SpaceLimitShapes
public import SerrePositivity.InfinityCategories.Stable.FunctorFiniteLimits
public import SerrePositivity.InfinityCategories.Stable.ExcisionRepresentableLimits

/-!
概要：選択した元の filtered 空間値余極限関手は、全有限単体集合形状の極限を保つ。
方針：空形状と cospan の全錐交換を同じ関手の保存へ移し、有限セルで帰納する。
規約：D の有限存在 API をこの一葉からのみ import し、交換の入力仮定を置かない。
使われ方：I-2 d′ の一般 coherent 有限極限交換と Ind 入力の定理化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open Presentable

/-- 小さい元の空間値図式の、全普遍余錐族から選ぶ余極限関手。 -/
def smallSpaceColimitFunctor (B : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  chosenColimitFunctor _ _ (fun p ↦ hasColimit_coherentSpaceDiagram p)

/-- 一般 filtered ∞ 添字の元の余極限関手は、任意の有限形状の指定全極限錐を保つ。 -/
lemma smallSpaceFilteredColimit_map_isLimit_finite
    (B : SSet.{u}) [Quasicategory B] [IsFilteredInfinity B]
    {K : SSet.{u + 1}} [K.Finite]
    {p : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (smallSpaceColimitFunctor B) c) := by
  let : HasFiniteLimits SpaceInfinity.{u} := excisionSpace_hasFiniteLimits
  let : HasFiniteLimits ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}) :=
    hasFiniteLimits_functorCategory _ _
  apply map_isLimit_finite_of_empty_pointCospan (smallSpaceColimitFunctor B) ?_ ?_ c hc
  · intro T p d hd
    apply map_isLimit_of_shapeIso (smallSpaceColimitFunctor B) (finiteExchangeEmptyLiftIso T)
      (fun q a ha ↦ ?_) d hd
    exact chosenColimit_map_isLimit_of_exchange
      (fun p ↦ hasColimit_coherentSpaceDiagram p) (hasSpaceLimitsOfShape _)
      (by
        intro F c hc hF
        exact coherentFilteredLimitExchangeShape_empty (Δ[0] : SSet.{u}) B F c hc
          (fun b ↦ hF (ULift.up b))) a ha
  · intro p d hd
    apply map_isLimit_of_shapeIso (smallSpaceColimitFunctor B) finiteExchangePointCospanLiftIso
      (fun q a ha ↦ ?_) d hd
    exact chosenColimit_map_isLimit_of_exchange
      (fun p ↦ hasColimit_coherentSpaceDiagram p) (hasSpaceLimitsOfShape _)
      (by
        intro F c hc hF
        exact coherentFilteredLimitExchangeShape_cospanHorn B F c hc
          (fun b ↦ hF (ULift.up b))) a ha

end SerrePositivity.InfinityCategories.F2.Ind
