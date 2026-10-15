module
public import SerrePositivity.DifferentialGraded.Module.ConeCompositionDesc

/-! # 合成coneの全dg自然な逆方向比較の受入検査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms complexConeComp_inner_boundary
#print axioms complexConeComp_outer_boundary
#print axioms moduleConeCompInnerElement
#print axioms moduleConeCompOuterElement
#print axioms moduleConeCompInnerElement_π
#print axioms moduleConeCompOuterElement_π
#print axioms moduleConeCompInnerElement_d
#print axioms moduleConeCompInnerDesc
#print axioms moduleConeCompInnerDesc_cochain
#print axioms moduleConeCompOuterElement_d
#print axioms moduleConeCompInv
#print axioms moduleConeCompInv_eval
#print axioms moduleConeComp_hom_inv
