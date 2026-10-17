module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtensionCoherence

/-! # 有限 cell 上の二つの導来延長計算の整合性の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms derivedExtensionUnderivedMap_naturality
#print axioms derivedExtensionUnderivedNatTrans
#print axioms homotopyDerivedExtensionComparison
#print axioms homotopyDerivedExtensionComparison_app
#print axioms homotopyDerivedExtensionComparison_isIso
#print axioms finiteCellHomotopyDerivedExtensionIso
