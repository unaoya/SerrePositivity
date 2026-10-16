module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletionEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion

/-! # Actual completion commutes with arbitrary restriction and preserves its original unit -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

/-- Extend the restricted original S-completion unit by the original R-completion reflection. -/
def derivedCompletionRestrictionComparison (X : ConcreteDerivedCategory S) :
    (derivedComplexCompletionFunctor R a).obj ((derivedRestrictScalars φ).obj X) ⟶
      (derivedRestrictScalars φ).obj ((derivedComplexCompletionFunctor S (φ a)).obj X) :=
  (derivedComplexCompletionFunctor R a).map
      ((derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X)) ≫
    (derivedComplexCompletionUnitIso R a _
      (restrictedDerivedCompletionObject_isComplete φ a X)).inv

/-- The comparison preserves the original actual completion units exactly. -/
@[reassoc] lemma derivedCompletionRestrictionComparison_unit
    (X : ConcreteDerivedCategory S) :
    (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) ≫
        derivedCompletionRestrictionComparison φ a X =
      (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) :=
  (derivedComplexCompletionHomEquiv R a _ _
    (restrictedDerivedCompletionObject_isComplete φ a X)).apply_symm_apply _

/-- The canonical unit-normalized comparison is always an isomorphism. -/
lemma derivedCompletionRestrictionComparison_isIso (X : ConcreteDerivedCategory S) :
    IsIso (derivedCompletionRestrictionComparison φ a X) := by
  dsimp only [derivedCompletionRestrictionComparison]
  have := derivedRestrictionCompletionUnit_map_isIso φ a X
  infer_instance

/-- Reflection uniqueness makes the actual comparisons natural in every derived morphism. -/
lemma derivedCompletionRestrictionComparison_naturality
    {X Y : ConcreteDerivedCategory S} (f : X ⟶ Y) :
    (derivedComplexCompletionFunctor R a).map ((derivedRestrictScalars φ).map f) ≫
        derivedCompletionRestrictionComparison φ a Y =
      derivedCompletionRestrictionComparison φ a X ≫
        (derivedRestrictScalars φ).map ((derivedComplexCompletionFunctor S (φ a)).map f) := by
  apply derivedComplexCompletionHom_ext R a (restrictedDerivedCompletionObject_isComplete φ a Y)
  have hr := (derivedComplexCompletionUnit R a).naturality ((derivedRestrictScalars φ).map f)
  simp only [CategoryTheory.Functor.id_map] at hr
  rw [← Category.assoc, ← hr, Category.assoc, derivedCompletionRestrictionComparison_unit,
    ← Category.assoc, derivedCompletionRestrictionComparison_unit,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  simpa only [CategoryTheory.Functor.id_map] using
    congrArg (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).naturality f)

/-- Arbitrary restriction commutes naturally with the actual derived completion functors. -/
def derivedCompletionRestrictionIso :
    derivedRestrictScalars φ ⋙ derivedComplexCompletionFunctor R a ≅
      derivedComplexCompletionFunctor S (φ a) ⋙ derivedRestrictScalars φ :=
  NatIso.ofComponents
    (F := derivedRestrictScalars φ ⋙ derivedComplexCompletionFunctor R a)
    (G := derivedComplexCompletionFunctor S (φ a) ⋙ derivedRestrictScalars φ)
    (fun X ↦ by
    have := derivedCompletionRestrictionComparison_isIso φ a X
    exact asIso (derivedCompletionRestrictionComparison φ a X))
    (fun {X Y} f ↦ by
      change (derivedComplexCompletionFunctor R a).map ((derivedRestrictScalars φ).map f) ≫
        derivedCompletionRestrictionComparison φ a Y = _
      exact derivedCompletionRestrictionComparison_naturality φ a f)

/-- The natural isomorphism, with the original standard units, satisfies the required diagram. -/
@[reassoc] lemma derivedCompletionRestrictionIso_unit (X : ConcreteDerivedCategory S) :
    (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) ≫
        (derivedCompletionRestrictionIso φ a).hom.app X =
      (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) :=
  derivedCompletionRestrictionComparison_unit φ a X

/-- In the reverse orientation the original restricted unit is sent to the original R-unit. -/
@[reassoc] lemma derivedCompletionRestrictionIso_inv_unit (X : ConcreteDerivedCategory S) :
    (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) ≫
        (derivedCompletionRestrictionIso φ a).inv.app X =
      (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) := by
  rw [← derivedCompletionRestrictionIso_unit φ a X, Category.assoc,
    Iso.hom_inv_id_app]
  erw [Category.comp_id]

/-- The same actual natural comparison is available in the standard bounded-above categories. -/
def boundedAboveCompletionRestrictionIso :
    boundedAboveDerivedRestrictScalars φ ⋙ boundedAboveDerivedCompletionFunctor R a ≅
      boundedAboveDerivedCompletionFunctor S (φ a) ⋙ boundedAboveDerivedRestrictScalars φ :=
  NatIso.ofComponents
    (F := boundedAboveDerivedRestrictScalars φ ⋙ boundedAboveDerivedCompletionFunctor R a)
    (G := boundedAboveDerivedCompletionFunctor S (φ a) ⋙ boundedAboveDerivedRestrictScalars φ)
    (fun X ↦ ObjectProperty.isoMk _ ((derivedCompletionRestrictionIso φ a).app X.obj))
    (fun {X Y} f ↦ by
      apply InducedCategory.hom_ext
      exact (derivedCompletionRestrictionIso φ a).hom.naturality f.hom)

/-- The bounded-above comparison preserves the original units in the bounded categories. -/
@[reassoc] lemma boundedAboveCompletionRestrictionIso_unit
    (X : DerivedCategory.Minus (ModuleCat.{u} S)) :
    (boundedAboveDerivedCompletionUnit R a).app ((boundedAboveDerivedRestrictScalars φ).obj X) ≫
        (boundedAboveCompletionRestrictionIso φ a).hom.app X =
      (boundedAboveDerivedRestrictScalars φ).map
        ((boundedAboveDerivedCompletionUnit S (φ a)).app X) := by
  apply InducedCategory.hom_ext
  exact derivedCompletionRestrictionIso_unit φ a X.obj

/-- The requested G8 orientation: complete and restrict, or restrict and complete. -/
def derivedRestrictionCompletionIso :
    derivedComplexCompletionFunctor S (φ a) ⋙ derivedRestrictScalars φ ≅
      derivedRestrictScalars φ ⋙ derivedComplexCompletionFunctor R a :=
  (derivedCompletionRestrictionIso φ a).symm

/-- The G8-oriented isomorphism preserves exactly the original standard units. -/
@[reassoc] lemma derivedRestrictionCompletionIso_unit (X : ConcreteDerivedCategory S) :
    (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) ≫
        (derivedRestrictionCompletionIso φ a).hom.app X =
      (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) :=
  derivedCompletionRestrictionIso_inv_unit φ a X

end SerrePositivity.DerivedCompletion
