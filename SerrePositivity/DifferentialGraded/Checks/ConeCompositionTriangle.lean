module
public import SerrePositivity.DifferentialGraded.Module.ConeCompositionTriangle

/-! # 合成cone三角形のdistinguished性の受入検査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms triangle_comp_shift_id_of_eq
#print axioms map_comp_shift_comm
#print axioms moduleEvaluation_registeredShift
#print axioms moduleConeCompSecondMap
#print axioms moduleConeCompSecondMap_eval
#print axioms moduleConeComp_inr_inv
#print axioms moduleConeComp_hom_connecting
#print axioms moduleConeCompTriangle
#print axioms moduleHomotopyConeCompTriangle
#print axioms moduleHomotopyConeComp_mor₃
#print axioms moduleHomotopyConeComp_second_hom
#print axioms moduleHomotopyConeCompTriangleIso
#print axioms moduleHomotopyConeCompTriangle_distinguished
