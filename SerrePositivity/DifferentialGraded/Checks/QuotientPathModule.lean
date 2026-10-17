module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathModule

/-! # path 加群と全次数作用の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms pathTensorRightDG
#print axioms pathTensorRight_uncurry
#print axioms pathModule
#print axioms pathModuleValueIso
#print axioms pathModule_action
#print axioms pathModule_action_value
#print axioms pathTensorRight_swap
#print axioms pathModuleFreeIso
