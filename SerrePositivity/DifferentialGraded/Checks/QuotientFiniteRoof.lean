module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiniteRoof

/-! # 比較 cone からの有限 cell roof の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms derivedFiniteCell_subset_univ
#print axioms finiteCellFactor_exists_denominator
#print axioms finiteCellRoof_of_cone_factorTarget
#print axioms quotientRepresentable_exists_finiteCellRoof
#print axioms finiteCellFactor_of_comparison_zero
#print axioms comparison_zero_exists_finiteCell_denominator
#print axioms quotientRepresentable_exists_triaRoof
#print axioms triaQuotient_map_eq_zero_of_representableComparison
