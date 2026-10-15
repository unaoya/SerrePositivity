import SerrePositivity.PerfectComplex.KoszulTensor
import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
universe u

-- Both public entry points retain the same chosen isomorphism, without regularity assumptions.
example {R : Type u} [CommRing R] (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    Adams.oneKoszulTensorConeIso a P = cochainTensorUnitScalarConeIso a P := rfl

assert_no_sorry SerrePositivity.cochainTensorUnitScalar_leftUnitor
assert_no_sorry SerrePositivity.cochainTensorUnitScalarConeIso
assert_no_sorry SerrePositivity.cochainTensorUnitScalarConeIso_fst
assert_no_sorry SerrePositivity.cochainTensorUnitScalarConeIso_snd
assert_no_sorry SerrePositivity.cochainTensorUnitScalarConeIso_naturality
assert_no_sorry SerrePositivity.Adams.oneKoszulTensorScalar_leftUnitor
assert_no_sorry SerrePositivity.Adams.oneKoszulTensorConeIso
assert_no_sorry SerrePositivity.Adams.koszulSuccTensorIso
assert_no_sorry SerrePositivity.boundedAboveDerivedTensorQuotientKoszulIso_naturality
assert_no_sorry SerrePositivity.restrictedDerivedQuotientKoszulIso_naturality

#print axioms SerrePositivity.cochainTensorUnitScalarConeIso_naturality
#print axioms SerrePositivity.restrictedDerivedQuotientKoszulIso_naturality
