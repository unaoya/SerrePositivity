module

public import SerrePositivity.InfinityCategories.Core.JoinLeftColimits
public import SerrePositivity.InfinityCategories.Core.JoinRightColimits
public import SerrePositivity.InfinityCategories.Core.FatJoinRightColimits
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality

/-!
概要：join の関手の単射保存と fat join 比較の自然変換。
方針：検証済みの射ごとの単射性と自然性を関手のデータに束ねる。
規約：既存の関手と比較射の公開名・型は変更しない。
使われ方：Kerodon Lemma 4.6.2.10 のセルと骨格の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の join の左変数の関手は単射を保つ。
方針：joinMap の単射性を使う。
規約：右因子 K は任意。
使われ方：Kerodon §4.6.2 のセルの包含。 -/
instance joinLeftFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (joinLeftFunctor K).PreservesMonomorphisms where
  preserves f _ := joinMap_mono f (𝟙 K)

/-- 概要：通常の join の右変数の関手は単射を保つ。
方針：joinMap の単射性を使う。
規約：左因子 K は任意。
使われ方：Kerodon §4.6.2 のセルの包含。 -/
instance joinRightFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (joinRightFunctor K).PreservesMonomorphisms where
  preserves f _ := joinMap_mono (𝟙 K) f

/-- 概要：fat join の左変数の関手は単射を保つ。
方針：左因子の単射保存を関手に束ねる。
規約：右因子 K は任意。
使われ方：Kerodon §4.6.2 のセルの包含。 -/
instance fatJoinLeftFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (fatJoinLeftFunctor K).PreservesMonomorphisms where
  preserves f _ := fatJoinMap_left_mono f K

/-- 概要：fat join の右変数の関手は単射を保つ。
方針：右因子の単射保存を関手に束ねる。
規約：左因子 K は任意。
使われ方：Kerodon §4.6.2 のセルの包含。 -/
instance fatJoinRightFunctor_preservesMonomorphisms (K : SSet.{u}) :
    (fatJoinRightFunctor K).PreservesMonomorphisms where
  preserves f _ := fatJoinMap_right_mono K f

/-- 概要：右因子を固定した fat join 比較は自然変換。
方針：比較射の自然性を左変数に適用する。
規約：右因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10 の無限の骨格。 -/
noncomputable def fatJoinComparisonLeftNat (K : SSet.{u}) :
    fatJoinLeftFunctor K ⟶ joinLeftFunctor K where
  app A := fatJoinComparison A K
  naturality _ _ f := fatJoinComparison_naturality f (𝟙 K)

/-- 概要：左因子を固定した fat join 比較は自然変換。
方針：比較射の自然性を右変数に適用する。
規約：左因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10 の無限の骨格。 -/
noncomputable def fatJoinComparisonRightNat (K : SSet.{u}) :
    fatJoinRightFunctor K ⟶ joinRightFunctor K where
  app A := fatJoinComparison K A
  naturality _ _ f := fatJoinComparison_naturality (𝟙 K) f

end SerrePositivity.InfinityCategories
