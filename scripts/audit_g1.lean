import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescent
import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
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


-- Bottom and top ideals are accepted without finite-generation hypotheses.
example {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (h : Function.Surjective ((adicReductionMap (⊥ : Ideal R) f).lTensor (R ⧸ (⊥ : Ideal R)))) :
    Function.Surjective f := surjective_of_faithfullyFlat_adicReduction ⊥ _ f h

example {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsPrecomplete (⊤ : Ideal R) M]
    [IsHausdorff (⊤ : Ideal R) N] (f : M →ₗ[R] N)
    (h : Function.Surjective ((adicReductionMap (⊤ : Ideal R) f).lTensor (R ⧸ (⊤ : Ideal R)))) :
    Function.Surjective f := surjective_of_faithfullyFlat_adicReduction ⊤ _ f h

-- Zero modules require neither completeness assumptions nor a nonzero coefficient ring.
example {R : Type*} [CommRing R] (I : Ideal R)
    (f : (Fin 0 → R) →ₗ[R] (Fin 0 → R))
    (h : Function.Surjective ((adicReductionMap I f).lTensor (R ⧸ I))) :
    Function.Surjective f := surjective_of_faithfullyFlat_adicReduction I _ f h

-- The unit generator is allowed; target separation retains its usual mathematical force.
example {R S C : Type*} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C]
    [IsPrecomplete (Ideal.span {algebraMap R S (1 : R)}) S]
    [IsHausdorff (Ideal.span {algebraMap R C (1 : R)}) C] (f : S →ₐ[R] C)
    (h : Function.Surjective
      ((principalAdicReductionMap (1 : R) f).lTensor (R ⧸ Ideal.span {(1 : R)}))) :
    Function.Surjective f := surjective_algHom_of_faithfullyFlat_principalReduction 1 _ f h

-- a=0, including the zero coefficient ring.
example {R : Type*} [CommRing R] [Subsingleton R] (f : R →ₐ[R] R)
    (h : Function.Surjective
      ((principalAdicReductionMap (0 : R) f).lTensor (R ⧸ Ideal.span {(0 : R)}))) :
    Function.Surjective f := surjective_algHom_of_faithfullyFlat_principalReduction 0 _ f h

-- A concrete nilpotent/zero-divisor case, using R'=R/(2) for R=ZMod 4.
private theorem complete_of_square_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) (hI : I ^ 2 = ⊥) : IsAdicComplete I M where
  haus' x hx := by simpa [hI] using hx 2
  prec' f hf := by
    refine ⟨f 2, ?_⟩
    intro n
    by_cases hn : n ≤ 2
    · exact hf hn
    · have heq : f 2 = f n := by simpa [hI] using hf (m := 2) (n := n) (by omega)
      rw [heq]

private noncomputable def quotientTensorSelfEquiv {R : Type*} [CommRing R] (I : Ideal R) :
    (R ⧸ I) ⊗[R] (R ⧸ I) ≃ₗ[R ⧸ I] R ⧸ I := by
  letI : Algebra (R ⧸ I) ((R ⧸ I) ⧸ I.map (algebraMap R (R ⧸ I))) :=
    Ideal.instAlgebraQuotient _ _
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R ⧸ I) I).symm.toLinearEquiv ≪≫ₗ
    (Ideal.quotientEquivAlgOfEq (R ⧸ I) (Ideal.map_quotient_self I)).toLinearEquiv ≪≫ₗ
    (AlgEquiv.quotientBot (R ⧸ I) (R ⧸ I)).toLinearEquiv

example : Function.Surjective (AlgHom.id (ZMod 4) (ZMod 4)) := by
  let I : Ideal (ZMod 4) := Ideal.span {2}
  have hI : I ^ 2 = ⊥ := by
    rw [show I = Ideal.span {(2 : ZMod 4)} from rfl, Ideal.span_singleton_pow]
    rw [show (2 : ZMod 4) ^ 2 = 0 by decide]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  let := complete_of_square_zero (M := ZMod 4) I hI
  let : Module.FaithfullyFlat (ZMod 4 ⧸ I) ((ZMod 4 ⧸ I) ⊗[ZMod 4] (ZMod 4 ⧸ I)) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ (quotientTensorSelfEquiv I)
  apply surjective_algHom_of_principal_residue_baseChange (2 : ZMod 4) (ZMod 4 ⧸ I)
  have hid : principalAdicReductionMap (2 : ZMod 4) (AlgHom.id (ZMod 4) (ZMod 4)) =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [hid, LinearMap.lTensor_id]
  exact Function.surjective_id
