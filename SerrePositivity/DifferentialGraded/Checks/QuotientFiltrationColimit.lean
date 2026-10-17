module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationColimit

/-! # 長さ filtration の逐次余極限の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms lengthDiagram
#print axioms exists_lengthSubmodule
#print axioms lengthCocone_eval_isColimit
#print axioms lengthCocone_isColimit
#print axioms lengthColimitIso
#print axioms lengthColimitIso_ι
