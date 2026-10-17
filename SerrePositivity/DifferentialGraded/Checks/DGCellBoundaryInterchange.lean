module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryInterchange

/-! # cell pathの先頭作用と境界挿入の反交換の公理監査 -/
@[expose] public section

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_assoc
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_left_unit
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_tail_cochain
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceMiddle_tail_anticommute
