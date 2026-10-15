module
public import SerrePositivity.DifferentialGraded.Module.ConeShiftTriangleOrdinary
public import SerrePositivity.DifferentialGraded.Module.TriangleShiftMap

/-! # 閉零加群圏の三角形shift比較の受入検査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms triangleShiftMapIso
#print axioms moduleTriangleShiftIsoMk
#print axioms moduleConeShift_connecting_id
#print axioms moduleConeTriangleShiftIso
