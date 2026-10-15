import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates
import Mathlib.Util.AssertNoSorry

open CategoryTheory HomologicalComplex SerrePositivity
universe u
variable {R : Type u} [CommRing R]
example (a : R) : Adams.oneKoszulXZeroIso a =
    DerivedCompletion.moduleConeSndIso (Adams.oneKoszulScalarMap a) 0 1 rfl
      (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) 1 (by decide)) ≪≫
      Adams.oneKoszulUnitSelfIso := rfl
example (a : R) : Adams.oneKoszulXNegOneIso a =
    DerivedCompletion.moduleConeFstIso (Adams.oneKoszulScalarMap a) (-1) 0 (by decide)
      (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) (-1) (by decide)) ≪≫
      Adams.oneKoszulUnitSelfIso := rfl
assert_no_sorry SerrePositivity.Adams.oneKoszulXZeroIso
assert_no_sorry SerrePositivity.Adams.oneKoszulXNegOneIso
assert_no_sorry SerrePositivity.Adams.oneKoszul_generator_d
assert_no_sorry SerrePositivity.DerivedCompletion.moduleConeFstIso_inv
assert_no_sorry SerrePositivity.DerivedCompletion.moduleConeSndIso_inv
#print axioms SerrePositivity.Adams.oneKoszul_generator_d
