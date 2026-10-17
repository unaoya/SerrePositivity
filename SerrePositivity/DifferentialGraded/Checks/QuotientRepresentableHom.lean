module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRepresentableHom

/-! # Verdier 商の代表対象への射の比較の監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms quotientRepresentableHomMap
#print axioms quotientRepresentableHomMap_map
#print axioms quotientRepresentableHomMap_precomp
#print axioms quotientRepresentableHomMap_surjective
#print axioms quotientRepresentableHomMap_eq_zero
#print axioms quotientRepresentableHomMap_injective
#print axioms quotientRepresentableHomEquiv
#print axioms quotientDerivedRepresentableHomEquiv
