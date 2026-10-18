module
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Stable.Suspension
public import SerrePositivity.InfinityCategories.Stable.SuspensionEquivalence
public import SerrePositivity.InfinityCategories.Stable.PastingShapes
public import SerrePositivity.InfinityCategories.Stable.PastingCofinality
public import SerrePositivity.InfinityCategories.Stable.PastingRightSpanComparison
public import SerrePositivity.InfinityCategories.Stable.PastingCornerJoinIso
public import SerrePositivity.InfinityCategories.Stable.PastingRightCocone
public import SerrePositivity.InfinityCategories.Stable.CartesianInitialBoundary
public import SerrePositivity.InfinityCategories.Stable.CoconeRestrictionEdges
public import SerrePositivity.InfinityCategories.Stable.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamilies

/-! # 安定 ∞ 圏の基盤

概要：零対象・余極限・fiber/cofiber から安定 ∞ 圏の基盤を構成する。
方針：A2 の join・slice の極限の一般論を用いる。
規約：HA §1.1 に従う。使われ方：h C の三角構造・完全関手と D(S) の安定性。
-/
