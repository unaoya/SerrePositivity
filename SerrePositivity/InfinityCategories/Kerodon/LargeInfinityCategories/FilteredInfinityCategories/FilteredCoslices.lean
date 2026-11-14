module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiniteJoin
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.DiagramNestedCoslice

/-!
概要：filtered ∞ 圏の有限図式の下の coslice は filtered。
方針：coslice の図式を join に展開し、有限 join の余錐を結合同型で戻す。
規約：固定された元の図式を厳密に保ち、通常の圏の nerve に制限しない。
使われ方：filtered な添字の余錐空間と cofinality。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：有限図式の coslice 内の有限図式は元の図式を保つ余錐を持つ。
方針：uncurry した join の図式の余錐を既存の二重 coslice の比較で戻す。
規約：元の二つの図式全体を固定する。
使われ方：coslice の filtered 性の余錐条件。 -/
lemma nonempty_cocone_in_filtered_coslice {K L C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] [K.Finite] [L.Finite]
    (p : K ⟶ C) (f : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) := by
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f)
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry f Δ[0] c⟩

/-- 概要：filtered ∞ 圏の有限図式の下の coslice は filtered。
方針：有限図式に対する余錐の構成を filtered 性に束ねる。
規約：p は任意の有限単体集合上の図式。
使われ方：filtered な余錐の添字と cofinality の比較。 -/
instance isFilteredInfinity_sliceUnder {K C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] [K.Finite] (p : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) where
  cocone_nonempty := nonempty_cocone_in_filtered_coslice p

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
