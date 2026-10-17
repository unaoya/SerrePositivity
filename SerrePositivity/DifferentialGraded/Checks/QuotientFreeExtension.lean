module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFreeExtension

/-! # 一対象環からの自由加群と相対 K-flat 計算の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms pointDGFunctor
#print axioms pointExtensionFreeFunctorIso
#print axioms pointExtensionRingIso
#print axioms dgExtension_relativeKFlat_quasiIso
#print axioms relativeKFlatExtensionComputation
#print axioms coefficientRingModule_relativeKFlat
#print axioms derivedFreeAtKFlatIso
