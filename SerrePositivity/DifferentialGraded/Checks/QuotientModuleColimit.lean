module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonModuleColimit

/-! # 加群圏での長さ余極限の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms lengthModuleDiagramEvaluationIso
#print axioms lengthModuleCocone_eval_isColimit
#print axioms lengthModuleCocone_isColimit
#print axioms lengthModuleColimitIso
#print axioms lengthModuleColimitIso_ι
