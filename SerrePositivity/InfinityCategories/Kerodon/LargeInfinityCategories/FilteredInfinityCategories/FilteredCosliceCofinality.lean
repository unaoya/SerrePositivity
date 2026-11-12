module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceCoproduct
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：filtered ∞ 圏の有限図式の coslice から元の ∞ 圏への射影は right cofinal。
方針：Quillen A の comma を二つの有限図式の和の coslice と厳密に比較する。
規約：元の頂点射影を使い、comma の弱可縮性を追加仮定しない。
使われ方：filtered 添字の余錐による余極限計算。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：二つの有限図式の coslice の頂点を揃えた引き戻しは弱可縮。
方針：図式の和の coslice の弱可縮性を実際の引き戻し同型で移す。
規約：両射影は元の指定図式の頂点射影。
使われ方：Quillen A の標準 comma の弱可縮性。 -/
lemma isWeaklyContractible_pullback_cosliceProjections {K L C : SSet.{u}}
    [K.Finite] [L.Finite] [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C]
    (p : K ⟶ C) (q : L ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_sliceUnder_of_filtered (coprod.desc p q)
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCoproduct_isPullback p q).isoPullback).isWeakHomotopyEquivalence
  exact he.weaklyContractible_iff.mp h

/-- 概要：有限図式の coslice の頂点射影は right cofinal。
方針：各頂点の標準 comma を和の図式の coslice と比較し、Quillen A を適用する。
規約：right cofinal は余極限を計算する向き。
使われ方：filtered 図式の余錐を添字にした余極限の制限。 -/
@[kerodon 06D0]
lemma isRightCofinal_sliceUnderProjection_of_filtered {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] (p : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro b
  exact isWeaklyContractible_pullback_cosliceProjections p (SSet.yonedaEquiv.symm b)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
