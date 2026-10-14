import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescent
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.AdicReduction
assert_no_sorry SerrePositivity.adicReductionMap
assert_no_sorry SerrePositivity.adicReductionMap_mkQ
assert_no_sorry SerrePositivity.adicReductionMap_comp_mkQ

open SerrePositivity

-- No finite generation hypothesis on I or on either module.
example {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) :
    AdicReduction I M →ₗ[R ⧸ I] AdicReduction I N := adicReductionMap I f
