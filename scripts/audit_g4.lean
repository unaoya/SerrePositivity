import SerrePositivity.CommutativeAlgebra.WittGhostInjective
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.witt_ghostMap_injective_of_mul_prime_injective
#print axioms SerrePositivity.witt_ghostMap_injective_of_mul_prime_injective

-- The exact G4 signature, including rings where p need not be a unit.
example (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    Function.Injective (WittVector.ghostMap (p := p) (R := A)) :=
  SerrePositivity.witt_ghostMap_injective_of_mul_prime_injective p A hp
