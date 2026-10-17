module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraded

/-! # 正の随伴次数部分の固定長 path 計算の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms lengthCutoff_fixed
#print axioms lengthCutoff_succ
#print axioms lengthLayerProjection_kernel
#print axioms lengthLayerProjection_surjective
#print axioms lengthLayerProjection_exact
#print axioms lengthLayer_isColimit
#print axioms lengthGradedIso
#print axioms lengthLayer_shortExact
#print axioms lengthGradedIso_π
