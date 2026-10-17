import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeScalarConeIso
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangePowerConeCompletionIso
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeScalarConeIso
#print axioms SerrePositivity.boundedAboveDerivedBaseChangePowerConeCompletionIso

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- n = 0 is really the cone of 1 and has zero homology, including the zero ring.
theorem audit_prop247_zero_stage
    {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ 0)).obj X)).obj) : x = 0 := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
    (boundedAboveDerivedBaseChangeScalarConeIso φ (a ^ 0) X)
  apply e.toLinearEquiv.injective
  rw [map_zero]
  change e.hom x = 0
  have h := derivedScalarCone_homology_annihilated B (φ (a ^ 0))
    ((boundedAboveDerivedBaseChange φ).obj X).obj i (e.hom x)
  simpa only [pow_zero, map_one, one_smul] using h

-- Every target coefficient is retained on the homology of every actual stage.
theorem audit_prop247_power_stage_coefficient
    {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) (b : B)
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ n)).obj X)).obj) :
    let e := (DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
      (boundedAboveDerivedBaseChangePowerConeCompletionIso φ a n X)
    e.hom (b • x) = b • e.hom x := by
  exact map_smul _ _ _

assert_no_sorry audit_prop247_zero_stage
assert_no_sorry audit_prop247_power_stage_coefficient
#print axioms audit_prop247_zero_stage
#print axioms audit_prop247_power_stage_coefficient
