module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFreeGeneration

/-! # 自由加群の導来生成の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms pointDerivedExtension_mem
#print axioms freeAtKFlat_finiteCellFactorTarget
#print axioms exists_coefficientKFlat_resolution
#print axioms freeAt_quasiIso_of_homKFlat
#print axioms freeAt_finiteCellFactorTarget_into
#print axioms positivePath_finiteCellFactorTarget
#print axioms positivePath_finiteCellFactorTarget_of_flat_zero
