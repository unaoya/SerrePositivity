module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinRightColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality

/-!
概要：join の関手の単射保存と fat join 比較の自然変換。
方針：検証済みの射ごとの単射性と自然性を関手のデータに束ねる。
規約：既存の関手と比較射の公開名・型は変更しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルと骨格の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：通常の join の左変数の関手は単射を保つ。
方針：joinMap の単射性を使う。
規約：右因子 K は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの包含。 -/
instance joinLeftFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor K).PreservesMonomorphisms where
  preserves f _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mono f (𝟙 K)

/-- 概要：通常の join の右変数の関手は単射を保つ。
方針：joinMap の単射性を使う。
規約：左因子 K は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの包含。 -/
instance joinRightFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightFunctor K).PreservesMonomorphisms where
  preserves f _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mono (𝟙 K) f

/-- 概要：fat join の左変数の関手は単射を保つ。
方針：左因子の単射保存を関手に束ねる。
規約：右因子 K は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの包含。 -/
instance fatJoinLeftFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinLeftFunctor K).PreservesMonomorphisms where
  preserves f _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap_left_mono f K

/-- 概要：fat join の右変数の関手は単射を保つ。
方針：右因子の単射保存を関手に束ねる。
規約：左因子 K は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの包含。 -/
instance fatJoinRightFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinRightFunctor K).PreservesMonomorphisms where
  preserves f _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap_right_mono K f

/-- 概要：右因子を固定した fat join 比較は自然変換。
方針：比較射の自然性を左変数に適用する。
規約：右因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限の骨格。 -/
noncomputable def fatJoinComparisonLeftNat (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinLeftFunctor K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor K where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A K
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison_naturality f (𝟙 K)

/-- 概要：左因子を固定した fat join 比較は自然変換。
方針：比較射の自然性を右変数に適用する。
規約：左因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限の骨格。 -/
noncomputable def fatJoinComparisonRightNat (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinRightFunctor K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightFunctor K where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K A
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison_naturality (𝟙 K) f

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
