module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.SmallJoin
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.SmallSimplicialShapes
public import SerrePositivity.InfinityCategories.Stable.DiagramNestedCoslice

/-!
概要：κ-filtered ∞ 圏の κ-small な図式の下の coslice は κ-filtered で弱可縮。
方針：κ-small join の余錐を二重 coslice の比較で戻す。
規約：正則 κ を明示し、元の図式全体を固定する。
使われ方：Kerodon 9.1.1.16、Indκ の添字と cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：κ-small な図式の coslice 内の κ-small な図式は余錐を持つ。
方針：二つの形状の join の小ささから元の ∞ 圏内で余錐を取り戻す。
規約：正則 κ と指定された二つの図式を保持する。
使われ方：coslice の κ-filtered 性。 -/
lemma nonempty_cocone_in_kappaFiltered_coslice {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K L C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    (hK : IsKappaSmall κ K) (hL : IsKappaSmall κ L)
    (p : K ⟶ C) (f : L ⟶ sliceUnder p) : Nonempty (JoinCocone f) := by
  obtain ⟨c⟩ := IsKappaFiltered.cocone_nonempty (isKappaSmall_join hκ hK hL)
    (sliceUnderUncurry f)
  exact ⟨diagramNestedCosliceDiagramCurry f Δ[0] c⟩

/-- 概要：κ-filtered ∞ 圏の κ-small な図式の coslice は κ-filtered。
方針：join から戻した余錐を全ての κ-small な試験形状について束ねる。
規約：元の固定図式を変更しない。使われ方：Kerodon 9.1.1.16。 -/
lemma isKappaFiltered_sliceUnder {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    (hK : IsKappaSmall κ K) (p : K ⟶ C) : IsKappaFiltered κ (sliceUnder p) where
  cocone_nonempty hL f := nonempty_cocone_in_kappaFiltered_coslice hκ hK hL p f

/-- 概要：κ-filtered ∞ 圏の κ-small な図式の coslice は弱可縮。
方針：κ-filtered 性から filtered 性を忘れ、一般の弱可縮性を使う。
規約：coslice の Kan 性は仮定しない。使われ方：κ 版の Quillen A の添字。 -/
lemma isWeaklyContractible_sliceUnder_of_kappaFiltered {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    (hK : IsKappaSmall κ K) (p : K ⟶ C) : IsWeaklyContractible (sliceUnder p) := by
  have := isKappaFiltered_sliceUnder hκ hK p
  have := isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (sliceUnder p)
  exact isWeaklyContractible_of_isFilteredInfinity (sliceUnder p)

end SerrePositivity.InfinityCategories.F2
