module
public import SerrePositivity.DifferentialGraded.Verdier.RetractSquare

/-! # retract 比較図式の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms comparisonRetractPreimage
#print axioms comparisonRetract_i_square
#print axioms comparisonRetract_r_square
#print axioms comparisonRetract_iff
#print axioms localTriaRetract_iff
#print axioms localPerfectRetract_iff
#print axioms localCompletedRetract_i
#print axioms localCompletedRetract_r
#print axioms localCompletedRetract_split
