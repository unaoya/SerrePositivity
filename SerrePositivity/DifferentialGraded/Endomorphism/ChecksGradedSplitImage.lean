module
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitImage

/-! # dg関手による全次数分裂の保存の公理監査 -/
public section
open SerrePositivity.DifferentialGraded

#print axioms endomorphismClosedElement_π
#print axioms gradedSplit_inclusion_retraction_element
#print axioms gradedSplit_section_projection_element
#print axioms gradedSplit_section_retraction_element
#print axioms gradedSplit_decomposition_element
#print axioms zeroHomComponent_forward
#print axioms zeroHomComponent_unit
#print axioms zeroHomComponent_closed
#print axioms zeroHomComponent_zero
#print axioms zeroHomComponent_add
#print axioms zeroHomComponent_naturality
#print axioms moduleGradedSplitOfHomElements
#print axioms dgModuleFunctor_closedElement
#print axioms dgModuleFunctorGradedSplit
