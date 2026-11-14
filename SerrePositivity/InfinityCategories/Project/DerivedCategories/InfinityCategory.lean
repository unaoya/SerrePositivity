module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.InfinityCategory

/-! Compatibility names used outside InfinityCategories; internal consumers use new names. -/

@[expose] public section

@[deprecated (since := "2026-11-12")]
deprecated_alias_util _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory

@[deprecated (since := "2026-11-12")]
deprecated_alias_util _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv
