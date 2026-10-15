import SerrePositivity.HomologicalAlgebra.CochainTensorSymmetry
import SerrePositivity.HomologicalAlgebra.CochainIdempotent
import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous
import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.cochainTensor
assert_no_sorry SerrePositivity.cochainTensorSymmetry
assert_no_sorry SerrePositivity.cochainTensorSymmetry_hom_comp
assert_no_sorry SerrePositivity.CochainIdempotent.imageMap
assert_no_sorry SerrePositivity.CochainIdempotent.inclusion_projection
#print axioms SerrePositivity.cochainTensorSymmetry_hom_comp
#print axioms SerrePositivity.CochainIdempotent.inclusion_projection

assert_no_sorry SerrePositivity.ιTensorObj_cochainTensorMap
assert_no_sorry SerrePositivity.cochainTensorSymmetry_naturality
assert_no_sorry SerrePositivity.cochainTensorBaseChangeIso
assert_no_sorry SerrePositivity.DifferentialGraded.complexMonoidalPreadditive
assert_no_sorry SerrePositivity.DifferentialGraded.complexMonoidalLinear
assert_no_sorry SerrePositivity.cochainTensorAssociator_inv_apply_ι_of_sum

open CategoryTheory MonoidalCategory SerrePositivity
universe u
example {R : Type u} [CommRing R]
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ≅ P') (f : Q ≅ Q') :
    cochainTensorIso e f = tensorIso e f := rfl
#print axioms SerrePositivity.cochainTensorBaseChangeIso
#print axioms SerrePositivity.DifferentialGraded.complexMonoidalLinear
