module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionScalarConeComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion

/-! # Actual principal completion and a different regular principal base change

The original base-change image of the completion unit defines the comparison.
Regularity concerns only the quotient coordinate, and no flatness is imposed.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

/-- Coefficient restriction preserves and reflects the actual derived completeness condition. -/
lemma derivedRestrictScalars_isComplete_iff {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (Y : ConcreteDerivedCategory S) :
    IsComplete R a ((derivedRestrictScalars φ).obj Y) ↔ IsComplete S (φ a) Y := by
  constructor
  · intro h
    apply (isComplete_iff_derivedComplexCompletionUnit_isIso S (φ a) Y).mpr
    have := derivedComplexCompletionUnit_isIso_of_isComplete R a _ h
    have hn := derivedRestrictionCompletionIso_unit φ a Y
    have : IsIso ((derivedRestrictScalars φ).map
        ((derivedComplexCompletionUnit S (φ a)).app Y) ≫
        (derivedRestrictionCompletionIso φ a).hom.app Y) := by
      rw [hn]
      infer_instance
    have : IsIso ((derivedRestrictScalars φ).map
        ((derivedComplexCompletionUnit S (φ a)).app Y)) :=
      IsIso.of_isIso_comp_right _ ((derivedRestrictionCompletionIso φ a).hom.app Y)
    exact isIso_of_reflects_iso _ (derivedRestrictScalars φ)
  · exact derivedRestrictScalars_isComplete φ a Y

variable (R : Type u) [CommRing R] (a b : R) (hb : IsSMulRegular R b)
local notation "D" => DerivedCategory.Minus (ModuleCat R)
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {b})
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {b}

include hb in
/-- Derived quotient by a regular b preserves completeness for an arbitrary a. -/
lemma derivedBaseChange_principal_isComplete (X : D) (hc : IsComplete R a X.obj) :
    IsComplete Q ((q) a) ((boundedAboveDerivedBaseChange (q)).obj X).obj := by
  apply (derivedRestrictScalars_isComplete_iff (q) a _).mp
  exact isComplete_of_iso R a (restrictedDerivedQuotientKoszulIso b hb X).symm
    (derivedScalarCone_isComplete R a b X.obj hc)

include hb in
/-- The original quotient of the a-completion unit is an a-completion equivalence over Q. -/
lemma completionQuotientUnit_map_isIso (X : D) :
    IsIso ((derivedComplexCompletionFunctor Q ((q) a)).map
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom)) := by
  let F := derivedComplexCompletionFunctor R a
  let f := (boundedAboveDerivedCompletionUnit R a).app X
  let g := ((boundedAboveDerivedBaseChange (q)).map f).hom
  let eX := restrictedDerivedQuotientKoszulIso b hb X
  let eY := restrictedDerivedQuotientKoszulIso b hb
    ((boundedAboveDerivedCompletionFunctor R a).obj X)
  have hn := restrictedDerivedQuotientKoszulIso_naturality b hb f
  change (derivedRestrictScalars (q)).map g ≫ eY.hom =
    eX.hom ≫ (derivedScalarConeFunctor R b).map f.hom at hn
  have hi := scalarCone_completionUnit_map_isIso R a b X
  have hi' : IsIso (F.map ((derivedScalarConeFunctor R b).map f.hom)) := by
    dsimp only [f, boundedAboveDerivedCompletionUnit, ObjectProperty.homMk]
    exact hi
  have hleft : IsIso (F.map ((derivedRestrictScalars (q)).map g) ≫ F.map eY.hom) := by
    rw [← F.map_comp, hn, F.map_comp]
    infer_instance
  have hrestricted : IsIso (F.map ((derivedRestrictScalars (q)).map g)) :=
    IsIso.of_isIso_comp_right _ (F.map eY.hom)
  have : IsIso ((derivedRestrictScalars (q)).map
      ((derivedComplexCompletionFunctor Q ((q) a)).map g)) :=
    (NatIso.isIso_map_iff (derivedRestrictionCompletionIso (q) a) g).mpr hrestricted
  exact isIso_of_reflects_iso _ (derivedRestrictScalars (q))

/-- Extend the original quotient of the completion unit over the quotient ring. -/
def completionQuotientBaseChangeComparison (X : D) :
    (derivedComplexCompletionFunctor Q ((q) a)).obj ((boundedAboveDerivedBaseChange (q)).obj X).obj ⟶
      ((boundedAboveDerivedBaseChange (q)).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj X)).obj :=
  (derivedComplexCompletionFunctor Q ((q) a)).map
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom) ≫
    (derivedComplexCompletionUnitIso Q ((q) a) _
      (derivedBaseChange_principal_isComplete R a b hb _
        (derivedComplexCompletionFunctor_isComplete R a X.obj))).inv

/-- The Q-linear comparison preserves the original base-change completion unit. -/
lemma completionQuotientBaseChangeComparison_unit (X : D) :
    (derivedComplexCompletionUnit Q ((q) a)).app ((boundedAboveDerivedBaseChange (q)).obj X).obj ≫
        completionQuotientBaseChangeComparison R a b hb X =
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom) :=
  (derivedComplexCompletionHomEquiv Q ((q) a) _ _
    (derivedBaseChange_principal_isComplete R a b hb _
      (derivedComplexCompletionFunctor_isComplete R a X.obj))).apply_symm_apply _

/-- The original comparison is an actual derived isomorphism over the quotient coefficient ring. -/
lemma completionQuotientBaseChangeComparison_isIso (X : D) :
    IsIso (completionQuotientBaseChangeComparison R a b hb X) := by
  dsimp only [completionQuotientBaseChangeComparison]
  have := completionQuotientUnit_map_isIso R a b hb X
  infer_instance

/-- Completion and regular principal base change commute on the original derived objects. -/
def completionQuotientBaseChangeIso (X : D) :
    (derivedComplexCompletionFunctor Q ((q) a)).obj ((boundedAboveDerivedBaseChange (q)).obj X).obj ≅
      ((boundedAboveDerivedBaseChange (q)).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj X)).obj := by
  have := completionQuotientBaseChangeComparison_isIso R a b hb X
  exact asIso (completionQuotientBaseChangeComparison R a b hb X)

end SerrePositivity.DerivedCompletion
