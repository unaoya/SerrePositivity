module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairZeroCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction
/-! # Remove an already complete coordinate from the actual two-coordinate H0

Completeness of the base for a is retained by principal b-completion. The original
ring universal properties give inverse algebra maps and preserve the original unit.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [CommRing R] (a b : R)
    (hc : IsModuleComplete R a (ModuleCat.of R R))

include hc in
/-- Principal b-completion preserves the base a-completeness. -/
lemma principalCompletionH0_isModuleComplete_first_of_base :
    IsModuleComplete R a (PrincipalCompletionH0 R b) := by
  exact principalCompletionH0_isModuleComplete_of_other R R a b hc

/-- The actual pair completion maps to the principal completion by its universal property. -/
def pairCompletionToPrincipalOfCompleteFirst :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PairCompletionH0 R a b →ₐ[R] PrincipalCompletionH0 R b := by
  letI := principalCompletionCommRing R b
  letI := principalCompletionAlgebra R b
  exact (pairCompletion_existsUnique_algHom R a b (PrincipalCompletionH0 R b)
    (principalCompletionH0_isModuleComplete_first_of_base R a b hc)
    (principalCompletionH0_isModuleComplete R b)).choose

/-- The principal completion maps to the actual pair completion. -/
def principalCompletionToPair :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PrincipalCompletionH0 R b →ₐ[R] PairCompletionH0 R a b := by
  letI := pairCompletionCommRing R a b
  letI := pairCompletionAlgebra R a b
  exact (principalCompletion_existsUnique_algHom R b (PairCompletionH0 R a b)
    (pairCompletionH0_isModuleComplete_second R a b)).choose

/-- The two universal maps compose to the identity on principal H0. -/
lemma pairCompletionToPrincipal_comp :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    (pairCompletionToPrincipalOfCompleteFirst R a b hc).comp (principalCompletionToPair R a b) =
      AlgHom.id R (PrincipalCompletionH0 R b) := by
  let := pairCompletionCommRing R a b
  let := pairCompletionAlgebra R a b
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  exact (principalCompletion_existsUnique_algHom R b (PrincipalCompletionH0 R b)
    (principalCompletionH0_isModuleComplete R b)).unique trivial trivial

/-- They also compose to the identity on the actual pair H0. -/
lemma principalCompletionToPair_comp :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    (principalCompletionToPair R a b).comp (pairCompletionToPrincipalOfCompleteFirst R a b hc) =
      AlgHom.id R (PairCompletionH0 R a b) := by
  let := pairCompletionCommRing R a b
  let := pairCompletionAlgebra R a b
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  exact (pairCompletion_existsUnique_algHom R a b (PairCompletionH0 R a b)
    (pairCompletionH0_isModuleComplete_first R a b)
    (pairCompletionH0_isModuleComplete_second R a b)).unique trivial trivial

/-- An already complete first coordinate can be removed on actual H0 algebras. -/
def pairCompletionPrincipalAlgEquivOfCompleteFirst :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PairCompletionH0 R a b ≃ₐ[R] PrincipalCompletionH0 R b := by
  letI := pairCompletionCommRing R a b
  letI := pairCompletionAlgebra R a b
  letI := principalCompletionCommRing R b
  letI := principalCompletionAlgebra R b
  exact AlgEquiv.ofAlgHom (pairCompletionToPrincipalOfCompleteFirst R a b hc)
    (principalCompletionToPair R a b) (pairCompletionToPrincipal_comp R a b hc)
    (principalCompletionToPair_comp R a b hc)

/-- The comparison preserves the original pair completion unit. -/
lemma pairCompletionPrincipalAlgEquivOfCompleteFirst_unit (r : R) :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    pairCompletionPrincipalAlgEquivOfCompleteFirst R a b hc (pairCompletionUnitRingHom R a b r) =
      principalCompletionUnitRingHom R b r := by
  let := pairCompletionCommRing R a b
  let := pairCompletionAlgebra R a b
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  exact (pairCompletionPrincipalAlgEquivOfCompleteFirst R a b hc).commutes r
end SerrePositivity.DerivedCompletion
