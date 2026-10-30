module
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # Ordinary residue factors in completed tensor base change under explicit regularity -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) (n : ℕ)
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (hS : IsSMulRegular S a) (hT : IsSMulRegular T a)
local notation "q" => Ideal.Quotient.mk (Ideal.span {a ^ n})

end SerrePositivity.DerivedCompletion
