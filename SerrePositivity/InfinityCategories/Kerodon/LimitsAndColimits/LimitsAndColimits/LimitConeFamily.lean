module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceConeFamilyEquivalence

/-!
概要：極限錐を錐の関手圏の fiber の終対象で判定する。
方針：slice との比較の同値で終対象性を移す。
規約：図式を高次単体でも固定する。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5）、Proposition 7.1.6.13（Tag 02XB） の絶対極限の準備。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：join の錐が極限錐であることと、固定図式上の錐の関手圏の終対象であることは同値。
方針：slice との比較の同値の終対象性の不変性と零単体の計算を使う。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の極限の関手圏による表示。 -/
lemma isLimitCone_iff_isTerminalVertex_coneFamily {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv p c) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap p).choose.isTerminalVertex_iff c
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_app_zero] at h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
