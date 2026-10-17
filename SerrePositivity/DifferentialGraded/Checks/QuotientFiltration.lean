module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltration

/-! # 最終 dg 商 Hom の長さ部分複体の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms lengthSubmodule_mono
#print axioms erasure_path_apply
#print axioms lengthSubmodule_d
#print axioms lengthComplex
#print axioms lengthInclusion
#print axioms lengthInclusion_mono
#print axioms lengthMap
#print axioms lengthMap_inclusion
#print axioms lengthMap_refl
#print axioms lengthMap_comp
#print axioms lengthSubmodule_erasure
#print axioms lengthSubmodule_exhaustive
