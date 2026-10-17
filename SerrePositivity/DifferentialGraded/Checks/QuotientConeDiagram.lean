module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonConeDiagram

/-! # 比較 cone の図式と成分の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms complexConeMap_fst
#print axioms complexConeMap_snd
#print axioms complexConeMap_f_injective
#print axioms complexConeMap_elementMk
#print axioms lengthComparisonConeDiagram
#print axioms lengthComparisonConeCocone
