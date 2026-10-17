module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRestriction

/-! # 商からの制限加群の acyclic 性の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms complex_acyclic_of_homotopy_isZero
#print axioms quotientModule_value_acyclic
#print axioms quotientModuleRestriction_value_acyclic
#print axioms quotientDerivedRestriction_homology_isZero
#print axioms quotientDerivedRestriction_representable_hom_subsingleton
