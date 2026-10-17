module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedTensor

/-! # 随伴次数部分の片側 tensor 表示の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms consLengthWordEquiv
#print axioms snocLengthWordEquiv
#print axioms fixedLengthPrefixIso
#print axioms fixedLengthSuffixIso
#print axioms lengthGradedPrefixIso
#print axioms lengthGradedSuffixIso
#print axioms pathCoproduct_acyclic
#print axioms fixedLengthHom_acyclic_into
#print axioms fixedLengthHom_acyclic_outOf
