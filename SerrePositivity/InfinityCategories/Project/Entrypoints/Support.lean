module
public import SerrePositivity.InfinityCategories.Derived.SupportBasic
public import SerrePositivity.InfinityCategories.Derived.SupportClosure
public import SerrePositivity.InfinityCategories.Derived.SupportZero
public import SerrePositivity.InfinityCategories.Derived.SupportScalar

public import SerrePositivity.InfinityCategories.Derived.FullSemifreeHomotopy
public import SerrePositivity.InfinityCategories.Derived.FullSemifreeCanonical
public import SerrePositivity.InfinityCategories.Derived.SupportHomotopy
public import SerrePositivity.InfinityCategories.Derived.SupportComparison
public import SerrePositivity.InfinityCategories.Derived.SupportBaseChangeComparison
public import SerrePositivity.InfinityCategories.Derived.SupportK0
public import SerrePositivity.InfinityCategories.Derived.SupportOperations

public import SerrePositivity.InfinityCategories.Derived.SupportCoproduct

/-! # 台つき導来 ∞ 圏

概要：コホモロジーの台で D_Z と Perf_Z を定義し、閉性と完全対象のスカラー台を公開する。
方針：semifree 複体の充満部分単体集合を用いる。
規約：一般の D_Z に一様な冪消去を課さない。使われ方：局所化と台つき K 理論の比較。
-/
