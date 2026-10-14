module
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Restriction of scalars detects actual derived isomorphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Exact restriction of scalars reflects isomorphisms on the entire derived category. -/
instance derivedRestrictScalars_reflectsIsomorphisms :
    (derivedRestrictScalars φ).ReflectsIsomorphisms where
  reflects {X Y} f := by
    intro hf
    apply (DerivedCategory.isIso_iff (ModuleCat S) f).mpr
    intro i
    have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((derivedRestrictScalars φ).map f)) := inferInstance
    have : IsIso ((ModuleCat.restrictScalars φ).map
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).map f)) := by
      have h := (NatIso.isIso_map_iff (derivedRestrictScalarsHomologyIso φ i) f).mp
        (by change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
          ((derivedRestrictScalars φ).map f)); infer_instance)
      exact h
    exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars φ)

/-- The same reflection holds after restricting to the bounded-above derived categories. -/
instance boundedAboveDerivedRestrictScalars_reflectsIsomorphisms :
    (boundedAboveDerivedRestrictScalars φ).ReflectsIsomorphisms where
  reflects {X Y} f := by
    intro hf
    have hi : IsIso (DerivedCategory.Minus.ι.map
        ((boundedAboveDerivedRestrictScalars φ).map f)) := inferInstance
    have : IsIso ((derivedRestrictScalars φ).map f.hom) := hi
    have hD : IsIso f.hom := isIso_of_reflects_iso f.hom (derivedRestrictScalars φ)
    have : IsIso (DerivedCategory.Minus.ι.map f) := hD
    exact isIso_of_reflects_iso f DerivedCategory.Minus.ι

end SerrePositivity
