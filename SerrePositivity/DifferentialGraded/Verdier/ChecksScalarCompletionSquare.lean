module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarCompletionSquare

/-! # 係数変更と Karoubi 完備化の経路比較の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms scalarCompletedTriaFunctorIsTriangulated
#print axioms scalarCompletedTriaSquare
#print axioms scalarCompletedPerfectSquare
#print axioms scalarCompletedLocalPerfectSquare
#print axioms scalarCompletionComparisonIso
#print axioms scalarCompletionToKaroubiSquare
