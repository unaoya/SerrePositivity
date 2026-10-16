import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionUpperBound
import Mathlib.Util.AssertNoSorry

open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.DerivedCompletion
universe u
attribute [local instance] HasDerivedCategory.standard

assert_no_sorry complexPowerKoszulStage_homology_isZero_of_gt
#print axioms complexPowerKoszulStage_homology_isZero_of_gt
assert_no_sorry complexPowerKoszulTransition_homology_top_surjective
#print axioms complexPowerKoszulTransition_homology_top_surjective
assert_no_sorry complexCompletion_homology_isZero_of_gt
#print axioms complexCompletion_homology_isZero_of_gt
assert_no_sorry derivedComplexCompletionFunctor_isLE
#print axioms derivedComplexCompletionFunctor_isLE
assert_no_sorry boundedAboveDerivedCompletionFunctor_isLE
#print axioms boundedAboveDerivedCompletionFunctor_isLE

-- Exact first G11 request, for the original bounded-above completion.
example {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (hX : X.obj.IsLE 0) :
    ((boundedAboveDerivedCompletionFunctor R a).obj X).obj.IsLE 0 :=
  boundedAboveDerivedCompletionFunctor_isLE R a X 0 hX

-- The same upper bound, with no arithmetic or completeness assumptions.
example {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (k : ℤ) (hX : X.obj.IsLE k) :
    ((boundedAboveDerivedCompletionFunctor R a).obj X).obj.IsLE k :=
  boundedAboveDerivedCompletionFunctor_isLE R a X k hX

-- The assertion also holds on the original unbounded derived category.
example {R : Type u} [CommRing R] (a : R)
    (X : ConcreteDerivedCategory R) (k : ℤ) (hX : X.IsLE k) :
    ((derivedComplexCompletionFunctor R a).obj X).IsLE k :=
  derivedComplexCompletionFunctor_isLE R a X k hX
