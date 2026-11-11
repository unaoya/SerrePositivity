module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullInputCospan
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedRetraction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionInitialReplacement
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionInitialReplacementSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionReplaceInitial_input_isPullback {X : SSet.{u}} [Quasicategory X]
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_isPullback_iff c _ _
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary_projection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding_initial).mpr
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary_mono.{u}
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_nerve_mono.{u}
  have : Mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary.{u} := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isLimitCone_iff_restrict_of_leftAnodyne c _
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullInputCospanBoundary_leftAnodyne).mp hc

lemma exists_excisionPullbackReplacement {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    ∃ G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X,
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ G =
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ G) := by
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit
    (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F)
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_restrict c,
    excisionReplaceInitial_input_isPullback c hc⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
