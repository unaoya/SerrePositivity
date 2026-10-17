module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtension

/-! # tria 上の実際の比較関手の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms finiteCellCode_image_mem
#print axioms graphExtension_cone_distinguished
#print axioms graphDerivedExtension_finiteCell_mem
#print axioms graphDerivedExtension_derivedFiniteCell_mem
#print axioms derivedComparisonTria
#print axioms derivedComparisonTria_representableIso
#print axioms derivedComparisonFromTria_kills
#print axioms derivedComparisonTria_kills
#print axioms derivedComparisonTria_generates
