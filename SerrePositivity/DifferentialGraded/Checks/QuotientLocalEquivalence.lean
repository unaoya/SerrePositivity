module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonEquivalence

/-! # 局所 K-flat 版の指定 Verdier 商同値の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms derivedQuotientLift_finiteCell
#print axioms localQuotientTriaFunctor
#print axioms localQuotientTriaFullyFaithful
#print axioms localQuotientTriaRepresentableIso
#print axioms localQuotientTriaFunctor_essSurj
#print axioms localQuotientTriaEquivalence
#print axioms localQuotientTriaEquivalence_of_flat_zero
