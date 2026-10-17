module
public import SerrePositivity.DifferentialGraded.Verdier.ShiftedHomComparison

/-! # Hom 全単射性の shift と同型による移送の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms homComparison_bijective_of_iso
#print axioms homComparison_bijective_shift_both
#print axioms homComparisonTargetClosedUnderIso
#print axioms homComparisonTargetStableUnderShift
