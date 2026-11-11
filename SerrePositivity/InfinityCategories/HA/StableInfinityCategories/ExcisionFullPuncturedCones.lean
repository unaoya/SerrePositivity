module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedRetraction
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

lemma excisionFullPunctured_cone_extension {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u} ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor ≫ F)) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone d (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor) = c ∧
        d.vertex = c.vertex := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_nerve_mono.{u}
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration F
    (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_leftAnodyne
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cone_extension_of_trivialRestriction _ _ c

lemma excisionFullPunctured_limitCone_extension {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u} ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor ≫ F))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone d (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor) = c ∧
        d.vertex = c.vertex := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_nerve_mono.{u}
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration F
    (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_leftAnodyne
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_limitCone_extension_of_trivialRestriction _ _ c hc

lemma excisionFullPunctured_limit_iff {X : SSet.{u}} [Quasicategory X]
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u} ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c
      (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor)) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_nerve_mono.{u}
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isLimitCone_iff_restrict_of_leftAnodyne c _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_leftAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
