import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescent
import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent
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

assert_no_sorry SerrePositivity.surjective_of_faithfullyFlat_adicReduction

-- E is only a module over the residue ring, not an algebra or an R-flat module.
example {R M N E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R)
    [IsPrecomplete I M] [IsHausdorff I N] [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.FaithfullyFlat (R ⧸ I) E] (f : M →ₗ[R] N)
    (h : Function.Surjective ((adicReductionMap I f).lTensor E)) :
    Function.Surjective f := surjective_of_faithfullyFlat_adicReduction I E f h

assert_no_sorry SerrePositivity.adicQuotientAlgebra
assert_no_sorry SerrePositivity.adicReductionEquivAlgebraQuotient
assert_no_sorry SerrePositivity.adicReductionEquivAlgebraQuotient_mkQ
assert_no_sorry SerrePositivity.adicReductionEquivAlgebraQuotient_symm_mk
assert_no_sorry SerrePositivity.adicAlgebraReductionMap
assert_no_sorry SerrePositivity.adicAlgebraReductionMap_mk
assert_no_sorry SerrePositivity.adicAlgebraReductionMap_equiv
assert_no_sorry SerrePositivity.surjective_algHom_of_faithfullyFlat_adicReduction
assert_no_sorry SerrePositivity.surjective_algHom_of_residue_baseChange
assert_no_sorry SerrePositivity.principalAdicQuotientAlgebra
assert_no_sorry SerrePositivity.principalAdicReductionEquiv
assert_no_sorry SerrePositivity.principalAdicReductionEquiv_mkQ
assert_no_sorry SerrePositivity.principalAdicReductionEquiv_symm_mk
assert_no_sorry SerrePositivity.principalAdicReductionMap
assert_no_sorry SerrePositivity.principalAdicReductionMap_mk
assert_no_sorry SerrePositivity.surjective_algHom_of_faithfullyFlat_principalReduction
assert_no_sorry SerrePositivity.surjective_algHom_of_principal_residue_baseChange

open scoped TensorProduct
attribute [local instance] adicQuotientAlgebra principalAdicQuotientAlgebra

-- The exact B4 G1 signature: completeness and separation over S/C themselves.
-- No primality or regularity of p, and no R-flatness of R', are assumed.
example {R S C R' : Type} [CommRing R] [CommRing S] [CommRing C] [CommRing R']
    [Algebra R S] [Algebra R C] [Algebra R R'] (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : S)}) S]
    [IsHausdorff (Ideal.span {(p : C)}) C]
    [Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)})
      ((R ⧸ Ideal.span {(p : R)}) ⊗[R] R')]
    (f : S →ₐ[R] C)
    (h : Function.Surjective
      ((principalAdicReductionMap (p : R) f).lTensor
        ((R ⧸ Ideal.span {(p : R)}) ⊗[R] R'))) : Function.Surjective f := by
  have : IsPrecomplete (Ideal.span {algebraMap R S (p : R)}) S := by
    simpa only [map_natCast] using
      (inferInstance : IsPrecomplete (Ideal.span {(p : S)}) S)
  have : IsHausdorff (Ideal.span {algebraMap R C (p : R)}) C := by
    simpa only [map_natCast] using
      (inferInstance : IsHausdorff (Ideal.span {(p : C)}) C)
  exact surjective_algHom_of_principal_residue_baseChange (p : R) R' f h
