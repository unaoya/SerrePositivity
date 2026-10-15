module
public import SerrePositivity.DifferentialGraded.Category.TensorMixed

/-! # tensor積の因子分解・混合交換則の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms dgTensor_first_then_second
#print axioms dgTensor_second_then_first
