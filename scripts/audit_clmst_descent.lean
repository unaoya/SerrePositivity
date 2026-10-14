import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
import SerrePositivity.HomologicalAlgebra.TwoCohomologyAnnihilator
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimOne_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimit_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimit_homology_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimit_homology_pow_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.homology_pow_annihilated_of_equiv_homotopyLimit
assert_no_sorry SerrePositivity.DerivedCompletion.derived_homology_pow_annihilated_of_iso_homotopyLimit

#print axioms SerrePositivity.DerivedCompletion.complexTowerHomotopyLimit_homology_pow_annihilated
#print axioms SerrePositivity.DerivedCompletion.derived_homology_pow_annihilated_of_iso_homotopyLimit

-- D5: abstract two-cohomology objects and actual module-map cones.
assert_no_sorry SerrePositivity.two_cohomology_scalar_product_eq_zero
assert_no_sorry SerrePositivity.two_cohomology_scalar_pow_eq_zero
assert_no_sorry SerrePositivity.two_cohomology_scalar_pow_eq_zero_of_iso_homotopyLimit
assert_no_sorry SerrePositivity.moduleMapConeScalar_pow_eq_zero_of_iso_homotopyLimit

open CategoryTheory SerrePositivity
attribute [local instance] HasDerivedCategory.standard

-- Only the cohomological bounds are inputs; a strict/projective representative is not.
example (R : Type) [CommRing R] (X : DerivedCategory (ModuleCat.{0} R))
    (a b : ℤ) (hab : a + 1 = b) [X.IsGE a] [X.IsLE b] (g : R) (N : ℕ)
    (ha : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{0} R) a).obj X, g ^ N • x = 0)
    (hb : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{0} R) b).obj X, g ^ N • x = 0) :
    g ^ (2 * N) • 𝟙 X = 0 := two_cohomology_scalar_pow_eq_zero R X a b hab g N ha hb

#print axioms SerrePositivity.two_cohomology_scalar_product_eq_zero
#print axioms SerrePositivity.moduleMapConeScalar_pow_eq_zero_of_iso_homotopyLimit
