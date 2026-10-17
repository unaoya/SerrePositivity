module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonZeroModule

/-! # 零段階の加群同型と代表加群比較の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms lengthZeroModule_naturality
#print axioms lengthZeroModuleMap
#print axioms lengthZeroModuleIso
#print axioms lengthZeroModuleMap_inclusion
