module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedProjection

/-! # 固定長 path 射影と最終微分の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms selectedInclusion_projection
#print axioms selectedInclusion_mem_length
#print axioms fixedLengthProjection_kills_lower
#print axioms fixedLengthProjection_erasure
#print axioms lengthLayerProjection
