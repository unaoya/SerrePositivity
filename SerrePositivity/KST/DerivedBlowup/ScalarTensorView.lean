module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.CommutativeAlgebra.Module.ScalarTensorView

/-! Compatibility names used outside InfinityCategories; internal consumers use new names. -/

@[expose] public section

@[deprecated (since := "2026-11-12")]
deprecated_alias_util _root_.SerrePositivity.KST.DerivedBlowup.scalarCoefficientView := _root_.SerrePositivity.CommutativeAlgebra.Module.scalarCoefficientView

@[deprecated (since := "2026-11-12")]
deprecated_alias_util _root_.SerrePositivity.KST.DerivedBlowup.scalarExtensionTensorView := _root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView

@[deprecated (since := "2026-11-12")]
deprecated_alias_util _root_.SerrePositivity.KST.DerivedBlowup.scalarRestrictionTensorView := _root_.SerrePositivity.CommutativeAlgebra.Module.scalarRestrictionTensorView

@[deprecated (since := "2026-11-12")]
deprecated_alias_util _root_.SerrePositivity.KST.DerivedBlowup.scalarExtensionTensorView_tmul := _root_.SerrePositivity.CommutativeAlgebra.Module.scalarExtensionTensorView_tmul
