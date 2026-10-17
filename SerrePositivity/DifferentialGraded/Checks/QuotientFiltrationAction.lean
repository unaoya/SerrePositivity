module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationAction

/-! # 全次数作用による長さ filtration の安定性の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms selectedPrepend
#print axioms selectedPrepend_inclusion
#print axioms selectedProjection_prepend
#print axioms lengthCutoff_prepend
#print axioms internalPrepend_mem_length
#print axioms quotientPrepend_mem_length
