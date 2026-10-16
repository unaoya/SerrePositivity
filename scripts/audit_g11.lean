import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionUpperBound
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison
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

assert_no_sorry completionH0HomEquiv
#print axioms completionH0HomEquiv
assert_no_sorry completionH0HomEquiv_apply
#print axioms completionH0HomEquiv_apply
assert_no_sorry completionH0HomEquiv_precomp
#print axioms completionH0HomEquiv_precomp
assert_no_sorry derivedComplexCompletion_h0_map_isIso
#print axioms derivedComplexCompletion_h0_map_isIso
assert_no_sorry boundedAboveDerivedCompletion_h0_map_isIso
#print axioms boundedAboveDerivedCompletion_h0_map_isIso

-- Exact second G11 request, for the original morphism and the original functor.
example {R : Type u} [CommRing R] (a : R)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hX : X.obj.IsLE 0) (hY : Y.obj.IsLE 0)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f.hom)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (((boundedAboveDerivedCompletionFunctor R a).map f).hom)) :=
  boundedAboveDerivedCompletion_h0_map_isIso R a f hX hY hf

-- Two successive principal completions, using precisely the same twice-mapped morphism.
example {R : Type u} [CommRing R] (p : ℕ) (d : R)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hX : X.obj.IsLE 0) (hY : Y.obj.IsLE 0)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f.hom)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (((boundedAboveDerivedCompletionFunctor R d).map
        ((boundedAboveDerivedCompletionFunctor R (p : R)).map f)).hom)) := by
  apply boundedAboveDerivedCompletion_h0_map_isIso R d
  · exact boundedAboveDerivedCompletionFunctor_isLE R (p : R) X 0 hX
  · exact boundedAboveDerivedCompletionFunctor_isLE R (p : R) Y 0 hY
  · exact boundedAboveDerivedCompletion_h0_map_isIso R (p : R) f hX hY hf
