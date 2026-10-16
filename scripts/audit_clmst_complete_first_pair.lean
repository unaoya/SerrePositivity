import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFirstPairComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionH0_isModuleComplete_first_of_base
assert_no_sorry SerrePositivity.DerivedCompletion.pairCompletionToPrincipalOfCompleteFirst
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionToPair
assert_no_sorry SerrePositivity.DerivedCompletion.pairCompletionToPrincipal_comp
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionToPair_comp
assert_no_sorry SerrePositivity.DerivedCompletion.pairCompletionPrincipalAlgEquivOfCompleteFirst
assert_no_sorry SerrePositivity.DerivedCompletion.pairCompletionPrincipalAlgEquivOfCompleteFirst_unit

#print axioms SerrePositivity.DerivedCompletion.principalCompletionH0_isModuleComplete_first_of_base
#print axioms SerrePositivity.DerivedCompletion.pairCompletionToPrincipalOfCompleteFirst
#print axioms SerrePositivity.DerivedCompletion.principalCompletionToPair
#print axioms SerrePositivity.DerivedCompletion.pairCompletionToPrincipal_comp
#print axioms SerrePositivity.DerivedCompletion.principalCompletionToPair_comp
#print axioms SerrePositivity.DerivedCompletion.pairCompletionPrincipalAlgEquivOfCompleteFirst
#print axioms SerrePositivity.DerivedCompletion.pairCompletionPrincipalAlgEquivOfCompleteFirst_unit

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (a b : R)
    (hc : IsModuleComplete R a (ModuleCat.of R R))

example :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PairCompletionH0 R a b ≃ₐ[R] PrincipalCompletionH0 R b :=
  pairCompletionPrincipalAlgEquivOfCompleteFirst R a b hc

example (r : R) :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    pairCompletionPrincipalAlgEquivOfCompleteFirst R a b hc (pairCompletionUnitRingHom R a b r) =
      principalCompletionUnitRingHom R b r :=
  pairCompletionPrincipalAlgEquivOfCompleteFirst_unit R a b hc r

-- The second coordinate need not be regular; zero is allowed.
example :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R 0
    letI := principalCompletionAlgebra R 0
    PairCompletionH0 R a 0 ≃ₐ[R] PrincipalCompletionH0 R 0 :=
  pairCompletionPrincipalAlgEquivOfCompleteFirst R a 0 hc
