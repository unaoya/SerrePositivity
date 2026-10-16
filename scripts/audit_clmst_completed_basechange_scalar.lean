import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeScalar
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.derivedCompletion_map_scalar_id
#print axioms SerrePositivity.DerivedCompletion.derivedCompletion_map_scalar_id
assert_no_sorry SerrePositivity.DerivedCompletion.boundedAboveCompletion_map_scalar_id
#print axioms SerrePositivity.DerivedCompletion.boundedAboveCompletion_map_scalar_id
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionIso
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionIso
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionIso_scalar
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionIso_scalar
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionHomologyIso
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionHomologyIso
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionHomologyIso_scalar
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTensorRestrictionHomologyIso_scalar

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

theorem audit_completed_baseChange_original_base_scalar
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) (r : R)
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X)).obj) :
    (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom (φ r • x) =
      r • (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom x := by
  exact (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom.hom.map_smul r x

-- Arbitrary nilpotent target scalars, including the zero-ring/exponent-zero boundary.
theorem audit_completed_baseChange_nilpotent_scalar_factor
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) (s : S) (k : ℕ) (hs : s ^ k = 0) :
    ∀ y : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X))).obj,
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ (s ^ k)))
            (𝟙 X)))).hom y = 0 := by
  intro y
  let e := completedBaseChangeTensorRestrictionHomologyIso φ a X i
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  let xS : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X)).obj := x
  have hx : s ^ k • xS = 0 := by rw [hs, zero_smul]
  have he := completedBaseChangeTensorRestrictionHomologyIso_scalar φ a X i (s ^ k) xS
  rw [hx] at he
  change e.hom 0 = _ at he
  rw [map_zero] at he
  exact he.symm

assert_no_sorry audit_completed_baseChange_original_base_scalar
assert_no_sorry audit_completed_baseChange_nilpotent_scalar_factor
#print axioms audit_completed_baseChange_original_base_scalar
#print axioms audit_completed_baseChange_nilpotent_scalar_factor

