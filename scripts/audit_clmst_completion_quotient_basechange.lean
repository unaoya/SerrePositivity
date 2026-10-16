import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotientBaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.derivedRestrictScalars_isComplete_iff
assert_no_sorry SerrePositivity.DerivedCompletion.derivedBaseChange_principal_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientUnit_map_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientBaseChangeIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.completionQuotientBaseChangeNatIso

#print axioms SerrePositivity.DerivedCompletion.derivedRestrictScalars_isComplete_iff
#print axioms SerrePositivity.DerivedCompletion.derivedBaseChange_principal_isComplete
#print axioms SerrePositivity.DerivedCompletion.completionQuotientUnit_map_isIso
#print axioms SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison
#print axioms SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison_unit
#print axioms SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison_isIso
#print axioms SerrePositivity.DerivedCompletion.completionQuotientBaseChangeIso
#print axioms SerrePositivity.DerivedCompletion.completionQuotientBaseChangeComparison_naturality
#print axioms SerrePositivity.DerivedCompletion.completionQuotientBaseChangeNatIso

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a b : R) (hb : IsSMulRegular R b)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))

-- Completion at zero is covered without flatness of the derived source.
example :
    (derivedComplexCompletionFunctor (R ⧸ Ideal.span {b})
        ((Ideal.Quotient.mk (Ideal.span {b})) 0)).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X).obj ≅
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj
        ((boundedAboveDerivedCompletionFunctor R 0).obj X)).obj :=
  completionQuotientBaseChangeIso R 0 b hb X

-- Quotient by the unit gives the zero ring and is included in the exact same API.
example :
    (derivedComplexCompletionFunctor (R ⧸ Ideal.span {(1 : R)})
        ((Ideal.Quotient.mk (Ideal.span {(1 : R)})) a)).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(1 : R)}))).obj X).obj ≅
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(1 : R)}))).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj X)).obj :=
  completionQuotientBaseChangeIso R a 1 (by intro x y h; simpa only [one_smul] using h) X
