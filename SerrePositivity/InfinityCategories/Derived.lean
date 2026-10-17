module
public import SerrePositivity.InfinityCategories.Derived.Semifree
public import SerrePositivity.InfinityCategories.Derived.SemifreeKProjective
public import SerrePositivity.InfinityCategories.Derived.SemifreeResolution
public import SerrePositivity.InfinityCategories.Derived.SemifreeSubcategory
public import SerrePositivity.InfinityCategories.Derived.DerivedComparison
public import SerrePositivity.InfinityCategories.Derived.Checks

/-! # Semifree 複体による導来圏の dg 表示

概要：semifree 複体の H⁰ と Mathlib の導来圏の同値を公開する。
方針：一点 dg 加群の射影性と解像度を複体に転送する。
規約：dg nerve には依存しない。使われ方：導来 ∞ 圏のホモトピー圏の比較の基盤。
-/
