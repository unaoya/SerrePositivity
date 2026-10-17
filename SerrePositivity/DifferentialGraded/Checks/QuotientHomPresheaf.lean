module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonHomPresheaf

/-! # 指定 Verdier 商上の Hom 反変関手の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms quotientRestrictionHomPresheaf
#print axioms quotientRestrictionHomPresheaf_inverts
#print axioms quotientRestrictionLocalizedHom
#print axioms quotientRestrictionLocalizedHomFactors
#print axioms quotientRestrictionLocalizedHomEquiv
#print axioms quotientRestrictionLocalizedHomEquiv_naturality
