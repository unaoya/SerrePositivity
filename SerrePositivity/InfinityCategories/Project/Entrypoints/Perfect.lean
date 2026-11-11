module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectDerivedImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectEnhancementComparison

/-! # 完全導来 ∞ 圏 Perf(S) の公開インターフェース

概要：D(S) の充満部分 Perf(S)、各演算の閉性、D4 の引き戻し判定と h Perf の像を公開する。
方針：有界有限射影複体のホモトピー代表を semifree dg nerve の全部分集合に制限する。
規約：h Perf は標準包含で h D(S) の充満部分圏となる。
使われ方：K 理論の G2 と U13 の既存 perfect dg 加群との比較。
-/
