module
public import SerrePositivity.Asymptotic.DGVerdier.OrderSquare

/-! # U17c の実際の比較正方形の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms orderSquare
#print axioms orderSquareCommShift
#print axioms triaKaroubiComparison_eq_orderSquare
#print axioms localPerfectKaroubiFirstEquivalenceIsTriangulated
#print axioms localPerfectPaperSequenceComparisonCommShift
#print axioms paperSequenceComparison_eq_orderSquare
#print axioms paperSequenceComparisonCommShift
#print axioms orderSquare_naturality_smul
#print axioms localPerfectOrderSquareCommShift
#print axioms localPerfectPaperSequenceComparison_eq
#print axioms orderSquareTriangle
#print axioms localPerfectOrderSquareTriangle
#print axioms paperSequenceComparisonTriangle
