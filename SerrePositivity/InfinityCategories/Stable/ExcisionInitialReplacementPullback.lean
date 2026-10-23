module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullInputCospan
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionReplaceInitial_input_isPullback {X : SSet.{u}} [Quasicategory X]
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (hc : IsLimitCone c) :
    IsPullbackSquare (excisionGridSquareEmbedding ≫ excisionReplaceInitial c) := by
  apply (excisionReplaceInitial_isPullback_iff c _ _
    excisionFullInputCospanBoundary_projection excisionGridSquareEmbedding_initial).mpr
  have := excisionCoreCospanBoundary_mono.{u}
  have := excisionCorePuncturedToFull_nerve_mono.{u}
  have : Mono excisionFullInputCospanBoundary.{u} := by
    unfold excisionFullInputCospanBoundary
    infer_instance
  exact (isLimitCone_iff_restrict_of_leftAnodyne c _
    excisionFullInputCospanBoundary_leftAnodyne).mp hc

lemma exists_excisionPullbackReplacement {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    ∃ G : nerve ExcisionGridIndex.{u} ⟶ X,
      nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ G =
        nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F ∧
          IsPullbackSquare (excisionGridSquareEmbedding ≫ G) := by
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit
    (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)
  exact ⟨excisionReplaceInitial c, excisionReplaceInitial_restrict c,
    excisionReplaceInitial_input_isPullback c hc⟩

end SerrePositivity.InfinityCategories
