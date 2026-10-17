module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationZero

/-! # 長さ零段の計算の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms originalHom_f_injective
#print axioms lengthSubmodule_zero
#print axioms lengthZeroLinearMap_bijective
#print axioms lengthZeroIso
#print axioms lengthZeroMap_inclusion
