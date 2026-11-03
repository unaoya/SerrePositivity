module
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedInitial
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedRetraction
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism

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

lemma excisionFullPunctured_cone_extension {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionFullPuncturedIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap excisionCorePuncturedToFull.toFunctor ≫ F)) :
    ∃ d : JoinCone F,
      restrictJoinCone d (nerveMap excisionCorePuncturedToFull.toFunctor) = c ∧
        d.vertex = c.vertex := by
  have := excisionCorePuncturedToFull_nerve_mono.{u}
  have := sliceOverRestrict_trivialKanFibration F
    (nerveMap excisionCorePuncturedToFull.toFunctor)
      excisionCorePuncturedToFull_leftAnodyne
  exact exists_cone_extension_of_trivialRestriction _ _ c

lemma excisionFullPunctured_limitCone_extension {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionFullPuncturedIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap excisionCorePuncturedToFull.toFunctor ≫ F))
    (hc : IsLimitCone c) :
    ∃ d : JoinCone F, IsLimitCone d ∧
      restrictJoinCone d (nerveMap excisionCorePuncturedToFull.toFunctor) = c ∧
        d.vertex = c.vertex := by
  have := excisionCorePuncturedToFull_nerve_mono.{u}
  have := sliceOverRestrict_trivialKanFibration F
    (nerveMap excisionCorePuncturedToFull.toFunctor)
      excisionCorePuncturedToFull_leftAnodyne
  exact exists_limitCone_extension_of_trivialRestriction _ _ c hc

lemma excisionFullPunctured_limit_iff {X : SSet.{u}} [Quasicategory X]
    {F : nerve ExcisionFullPuncturedIndex.{u} ⟶ X} (c : JoinCone F) :
    IsLimitCone c ↔ IsLimitCone (restrictJoinCone c
      (nerveMap excisionCorePuncturedToFull.toFunctor)) := by
  have := excisionCorePuncturedToFull_nerve_mono.{u}
  exact isLimitCone_iff_restrict_of_leftAnodyne c _ excisionCorePuncturedToFull_leftAnodyne

end SerrePositivity.InfinityCategories
