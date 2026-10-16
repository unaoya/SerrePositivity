import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionH0_smul_injective_of_regular
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionH0_isAdicComplete_of_regular
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionToAdic
assert_no_sorry SerrePositivity.DerivedCompletion.adicCompletionToPrincipal
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionToAdic_comp_adicCompletionToPrincipal
assert_no_sorry SerrePositivity.DerivedCompletion.adicCompletionToPrincipal_comp_principalCompletionToAdic
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionAdicAlgEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.principalCompletionAdicAlgEquiv_unit

#print axioms SerrePositivity.DerivedCompletion.principalCompletionH0_smul_injective_of_regular
#print axioms SerrePositivity.DerivedCompletion.principalCompletionH0_isAdicComplete_of_regular
#print axioms SerrePositivity.DerivedCompletion.principalCompletionToAdic
#print axioms SerrePositivity.DerivedCompletion.adicCompletionToPrincipal
#print axioms SerrePositivity.DerivedCompletion.principalCompletionToAdic_comp_adicCompletionToPrincipal
#print axioms SerrePositivity.DerivedCompletion.adicCompletionToPrincipal_comp_principalCompletionToAdic
#print axioms SerrePositivity.DerivedCompletion.principalCompletionAdicAlgEquiv
#print axioms SerrePositivity.DerivedCompletion.principalCompletionAdicAlgEquiv_unit

noncomputable section
universe u
open SerrePositivity SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a)

example : Function.Injective (fun x : PrincipalCompletionH0 R a => a • x) :=
  principalCompletionH0_smul_injective_of_regular R a ha

example : IsAdicComplete (Ideal.span {a}) (PrincipalCompletionH0 R a) :=
  principalCompletionH0_isAdicComplete_of_regular R a ha

example :
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PrincipalCompletionH0 R a ≃ₐ[R] AdicCompletion (Ideal.span {a}) R :=
  principalCompletionAdicAlgEquiv R a ha

example (r : R) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    principalCompletionAdicAlgEquiv R a ha (principalCompletionUnitRingHom R a r) =
      algebraMap R (AdicCompletion (Ideal.span {a}) R) r :=
  principalCompletionAdicAlgEquiv_unit R a ha r
