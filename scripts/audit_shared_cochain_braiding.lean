import SerrePositivity.DifferentialGraded.Checks.Braiding
import SerrePositivity.HomologicalAlgebra.DerivedTensorBraided
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
universe u

example {R : Type u} [CommRing R] :
    DifferentialGraded.complexSymmetricCategory (A := R) =
      cochainTensorSymmetricCategory (R := R) := rfl

assert_no_sorry SerrePositivity.cochainTensorSymmetricCategory
assert_no_sorry SerrePositivity.DifferentialGraded.signedSwap_hexagon_forward
assert_no_sorry SerrePositivity.DifferentialGraded.signedSwap_hexagon_reverse
assert_no_sorry SerrePositivity.DifferentialGraded.complexSymmetricCategory
assert_no_sorry SerrePositivity.DifferentialGraded.braiding_eq_existing
assert_no_sorry SerrePositivity.boundedAboveDerivedSymmetricCategory
#print axioms SerrePositivity.cochainTensorSymmetricCategory
#print axioms SerrePositivity.DifferentialGraded.complexSymmetricCategory
#print axioms SerrePositivity.boundedAboveDerivedSymmetricCategory
