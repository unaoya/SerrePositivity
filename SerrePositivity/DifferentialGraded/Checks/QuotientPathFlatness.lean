module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathFlatness

/-! # 片側局所 K-flat 仮定からの path 係数の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms term_kFlat_into
#print axioms term_kFlat_outOf
#print axioms termSnocWeightIso
#print axioms pathPrefixWeight_kFlat
#print axioms pathSuffixWeight_kFlat
#print axioms pathPrefixWeight_tensor_acyclic
#print axioms pathPrefixWeight_tensor_quasiIso
#print axioms pathSuffixWeight_tensor_quasiIso
