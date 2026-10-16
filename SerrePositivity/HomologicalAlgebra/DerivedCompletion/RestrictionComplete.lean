module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction

/-! # Arbitrary coefficient restriction preserves actual derived completeness -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

/-- Restricting the original complete complex model gives an actually complete R-derived object. -/
lemma restrictedComplexCompletionObject_isComplete
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    IsComplete R a ((derivedRestrictScalars φ).obj (complexCompletionObject S (φ a) K)) := by
  let e : (derivedRestrictScalars φ).obj (complexCompletionObject S (φ a) K) ≅
      complexCompletionObject R a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) :=
    (derivedRestrictScalarsFactors φ).app ((complexCompletionFunctor S (φ a)).obj K) ≪≫
      DerivedCategory.Q.mapIso (restrictionComplexCompletionIso φ a K)
  exact isComplete_of_iso R a e.symm (complexCompletionObject_isComplete R a _)

/-- The restricted actual S-completion is R-complete, for every unbounded derived source. -/
lemma restrictedDerivedCompletionObject_isComplete
    (X : ConcreteDerivedCategory S) :
    IsComplete R a ((derivedRestrictScalars φ).obj
      ((derivedComplexCompletionFunctor S (φ a)).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : complexCompletionObject S (φ a) K ≅
      (derivedComplexCompletionFunctor S (φ a)).obj X :=
    (derivedComplexCompletionComparison S (φ a)).symm.app K ≪≫
      (derivedComplexCompletionFunctor S (φ a)).mapIso (DerivedCategory.Q.objObjPreimageIso X)
  exact isComplete_of_iso R a ((derivedRestrictScalars φ).mapIso e)
    (restrictedComplexCompletionObject_isComplete φ a K)

/-- Arbitrary coefficient restriction preserves the original derived completeness condition. -/
lemma derivedRestrictScalars_isComplete (X : ConcreteDerivedCategory S)
    (hX : IsComplete S (φ a) X) :
    IsComplete R a ((derivedRestrictScalars φ).obj X) :=
  isComplete_of_iso R a
    ((derivedRestrictScalars φ).mapIso (derivedComplexCompletionUnitIso S (φ a) X hX)).symm
    (restrictedDerivedCompletionObject_isComplete φ a X)

end SerrePositivity.DerivedCompletion
