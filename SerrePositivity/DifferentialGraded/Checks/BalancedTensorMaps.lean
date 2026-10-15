module
public import SerrePositivity.DifferentialGraded.Tensor.Maps

/-! # balanced tensorの両変数の降下mapと法則の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms BalancedTensor.generatorMap
#print axioms BalancedTensor.relationMap
#print axioms BalancedTensor.relationLeft_naturality
#print axioms BalancedTensor.relationRight_naturality
#print axioms BalancedTensor.mapOfFamilies
#print axioms BalancedTensor.ι_mapOfFamilies
#print axioms BalancedTensor.mapOfFamilies_id
#print axioms BalancedTensor.mapOfFamilies_comp
