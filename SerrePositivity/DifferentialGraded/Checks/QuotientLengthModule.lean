module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthModule

/-! # 長さ部分加群の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms quotientPrepend_composition
#print axioms quotientRepresentableRestriction_action
#print axioms lengthModuleMap
#print axioms lengthModuleMap_inclusion
#print axioms lengthModuleMap_inclusion_v
#print axioms lengthModuleMap_id
#print axioms lengthModuleMap_comp
#print axioms lengthModule
#print axioms lengthModuleInclusion
#print axioms lengthModuleInclusion_mono
#print axioms lengthModuleTransition
#print axioms lengthModuleTransition_inclusion
#print axioms lengthModuleDiagram
#print axioms lengthModuleCocone
