import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulStage
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
universe u
variable {R : Type u} [CommRing R]

example (f : R) (n : ℕ) :
    DerivedCompletion.powerKoszulTower R (fun _ : Fin 1 => f) n =
      Adams.oneKoszulComplex (f ^ n) := rfl
example (f : R) (n : ℕ) :
    DerivedCompletion.principalKoszulStageNegIso R f n =
      Adams.oneKoszulXNegOneIso (f ^ n) := rfl
example (f : R) (n : ℕ) :
    DerivedCompletion.principalKoszulStageZeroIso R f n =
      Adams.oneKoszulXZeroIso (f ^ n) := rfl
assert_no_sorry SerrePositivity.Adams.oneKoszul_generator_d
assert_no_sorry SerrePositivity.DerivedCompletion.principalKoszulStage_d
assert_no_sorry SerrePositivity.DerivedCompletion.principalKoszulStageNeg_transition
assert_no_sorry SerrePositivity.DerivedCompletion.principalKoszulStageZero_transition
#print axioms SerrePositivity.DerivedCompletion.principalKoszulStage_d
#print axioms SerrePositivity.DerivedCompletion.principalKoszulStageNeg_transition
