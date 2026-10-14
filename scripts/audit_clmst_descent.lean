import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
import SerrePositivity.HomologicalAlgebra.TwoCohomologyAnnihilator
import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion
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

-- D1: arbitrary rings and arbitrary torsion test modules, all exponents including zero.
assert_no_sorry SerrePositivity.torModule_subsingleton_of_completelyFlat_powerTorsion
assert_no_sorry SerrePositivity.isCompletelyFlat_principal_power
assert_no_sorry SerrePositivity.flat_residueTensor_of_completelyFlat
assert_no_sorry SerrePositivity.flat_power_residueTensor_of_completelyFlat
assert_no_sorry SerrePositivity.isCompletelyFlat_principal_ideal_pow
assert_no_sorry SerrePositivity.flat_algebraQuotient_of_completelyFlat
assert_no_sorry SerrePositivity.flat_power_algebraQuotient_of_completelyFlat

open scoped TensorProduct
attribute [local instance] adicQuotientAlgebra

-- No flatness of the original R-module, finiteness, or regularity of a is assumed.
example (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hM : IsCompletelyFlat (Ideal.span {a}) M) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {a ^ n}) ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) :=
  flat_power_residueTensor_of_completelyFlat a M hM n

-- Ring quotient actions use exactly the G1 interface's canonical residue algebra.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) (hS : IsCompletelyFlat (Ideal.span {a}) S) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {a ^ n})
      (S ⧸ (Ideal.span {a ^ n}).map (algebraMap R S)) :=
  flat_power_algebraQuotient_of_completelyFlat a S hS n

-- The zero-th stage is a quotient by a unit, without a nontriviality assumption.
example (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hM : IsCompletelyFlat (Ideal.span {a}) M) :
    Module.Flat (R ⧸ Ideal.span {a ^ 0}) ((R ⧸ Ideal.span {a ^ 0}) ⊗[R] M) :=
  flat_power_residueTensor_of_completelyFlat a M hM 0

#print axioms SerrePositivity.torModule_subsingleton_of_completelyFlat_powerTorsion
#print axioms SerrePositivity.flat_residueTensor_of_completelyFlat
#print axioms SerrePositivity.flat_power_algebraQuotient_of_completelyFlat
