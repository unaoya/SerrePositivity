module
public import SerrePositivity.DifferentialGraded.Complexes.ConeShift
public import SerrePositivity.DifferentialGraded.Module.ShiftElements
public import SerrePositivity.DifferentialGraded.Module.ShiftCompatibility

/-! # cone shiftの複体比較と豊穣shiftの公理監査 -/

open SerrePositivity.DifferentialGraded
#print axioms complexConeShiftIso
#print axioms complexConeShiftIso_hom_cochain
#print axioms complexConeShiftIso_inv_cochain
#print axioms complexConeShift_lift_condition
#print axioms complexConeShift_desc_condition
#print axioms complexConeShift_inr
#print axioms complexConeShift_connecting
#print axioms moduleShiftHomElement_π
#print axioms moduleShiftHomElement_d
#print axioms moduleHomotopyShiftAdditive
#print axioms moduleEvaluation_shiftComm
