module
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles

/-! # K(D)の評価関手の三角性の受入検査 -/
@[expose] public section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (x : D) : (moduleHomotopyEvaluation A D x).IsTriangulated := inferInstance
#print axioms mapTriangleSquareIso
#print axioms moduleHomotopyEvaluationFacIso
#print axioms moduleHomotopyEvaluationFacIsoCommShift
#print axioms moduleHomotopyConeTriangleEvaluationIso
#print axioms moduleHomotopyEvaluationIsTriangulated
