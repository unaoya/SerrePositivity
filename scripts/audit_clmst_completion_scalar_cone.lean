import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionScalarConeComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.derivedScalarCone_isComplete
assert_no_sorry SerrePositivity.DerivedCompletion.scalarCone_completionUnit_map_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionScalarConeComparison
assert_no_sorry SerrePositivity.DerivedCompletion.completionScalarConeComparison_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completionScalarConeComparison_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionScalarConeIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionScalarConeComparison_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.completionScalarConeNatIso

#print axioms SerrePositivity.DerivedCompletion.derivedScalarCone_isComplete
#print axioms SerrePositivity.DerivedCompletion.scalarCone_completionUnit_map_isIso
#print axioms SerrePositivity.DerivedCompletion.completionScalarConeComparison
#print axioms SerrePositivity.DerivedCompletion.completionScalarConeComparison_unit
#print axioms SerrePositivity.DerivedCompletion.completionScalarConeComparison_isIso
#print axioms SerrePositivity.DerivedCompletion.completionScalarConeIso
#print axioms SerrePositivity.DerivedCompletion.completionScalarConeComparison_naturality
#print axioms SerrePositivity.DerivedCompletion.completionScalarConeNatIso

noncomputable section
universe u
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a b : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))

-- A zero scalar cone is included, without regularity or purity assumptions on X.
example :
    (derivedComplexCompletionFunctor R a).obj ((derivedScalarConeFunctor R 0).obj X.obj) ≅
      (derivedScalarConeFunctor R 0).obj ((derivedComplexCompletionFunctor R a).obj X.obj) :=
  completionScalarConeIso R a 0 X

-- The completion coordinate can also be zero.
example :
    (derivedComplexCompletionUnit R 0).app ((derivedScalarConeFunctor R b).obj X.obj) ≫
        completionScalarConeComparison R 0 b X =
      (derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R 0).app X.obj) :=
  completionScalarConeComparison_unit R 0 b X
