module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFullFaithful

/-! # 局所 K-flat の導来延長の因子化の充満忠実性の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms derivedQuotientLiftCommShift
#print axioms derivedQuotientLiftIsTriangulated
#print axioms derivedQuotientLift_representable_target
#print axioms derivedQuotientLift_shifted_representable_target
#print axioms derivedQuotientLift_map_bijective
#print axioms derivedQuotientLiftFullyFaithful
