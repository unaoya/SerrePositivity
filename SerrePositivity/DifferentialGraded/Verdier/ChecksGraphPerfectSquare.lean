module
public import SerrePositivity.DifferentialGraded.Verdier.GraphKernelSquare

/-! # graph 作用の実際の Verdier・Karoubi・perfect 比較の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms quotientDGFunctor
#print axioms quotientDGFunctor_inclusion
#print axioms quotientDGFunctor_epsilon
#print axioms graphRestrictionCompositionIso
#print axioms derivedGraphRestrictionCompositionIso
#print axioms derivedGraphExtensionCompositionIso
#print axioms graphTriaFunctor_image
#print axioms graphVerdierFunctorIsTriangulated
#print axioms graphDerivedQuotientSquare
#print axioms graphLocalVerdierSquare
#print axioms graphCanonicalVerdierSquare
#print axioms karoubiFunctorSquare
#print axioms triaKaroubiPerfectSquare
#print axioms quotientScalarKaroubiPerfectSquare
#print axioms graphKaroubiPerfectSquare
#print axioms graphCompletedVerdierSquare
#print axioms graphCompletedPerfectSquare
#print axioms graphQuotientPerfectHomotopySquareCommShift
#print axioms graphQuotientPerfectHomotopySquareTriangle
#print axioms graphLocalPerfectSquare
#print axioms graphKernelQuotientSquare
#print axioms graphKernelQuotientSquare_naturality
