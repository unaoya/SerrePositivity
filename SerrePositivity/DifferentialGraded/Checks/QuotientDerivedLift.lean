module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonDerivedLift

/-! # 導来延長の実際の因子化関手と Hom 同値の一致の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms derivedComparisonFromTria_inverts
#print axioms derivedQuotientLift
#print axioms derivedQuotientLiftFactors
#print axioms derivedQuotientLiftRepresentableMap_map
#print axioms derivedQuotientLiftRepresentableMap_precomp
#print axioms derivedQuotientLiftRepresentableMap_eq
#print axioms derivedQuotientLiftRepresentableMap_bijective
#print axioms derivedQuotientLift_map_bijective_representable
