module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonCanonical

/-! # 指定比較関手そのものの局所 K-flat 同値の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms quotientTriaDerivedModelsIso
#print axioms quotientTriaModelsIso
#print axioms localQuotientTriaFactors
#print axioms quotientComparisonModelsIso
#print axioms quotientVerdierComparisonFullyFaithful
#print axioms quotientVerdierLocalEquivalence
#print axioms quotientVerdierLocalEquivalenceIsTriangulated
