module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetractTriangle

/-! # retractと補対象の三角形のcone表示の公理監査 -/
public section
open SerrePositivity.DifferentialGraded
#print axioms ringDerivedRetract_complement
#print axioms ringDerived_chainMap_homology_epi
#print axioms ringDerived_homology_biprodMap_epi
#print axioms ringDerivedTriangle_sum_coneRetract
