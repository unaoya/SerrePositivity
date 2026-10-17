import SerrePositivity.CLMST.PerfectoidIdealExcisionTor
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.algHom_isPullback_pullback
assert_no_sorry SerrePositivity.linearMap_ker_coker_annihilated_of_type_isPullback
assert_no_sorry SerrePositivity.algHom_ker_coker_annihilated_of_isPullback
assert_no_sorry SerrePositivity.perfectoidIdeal_ker_coker_annihilated_of_isPullback
assert_no_sorry SerrePositivity.perfectoidIdeal_ker_coker_annihilated_pullbackFst
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_TorInput_iff_of_isPullback
#print axioms SerrePositivity.algHom_isPullback_pullback
#print axioms SerrePositivity.linearMap_ker_coker_annihilated_of_type_isPullback
#print axioms SerrePositivity.algHom_ker_coker_annihilated_of_isPullback
#print axioms SerrePositivity.perfectoidIdeal_ker_coker_annihilated_of_isPullback
#print axioms SerrePositivity.perfectoidIdeal_ker_coker_annihilated_pullbackFst
#print axioms SerrePositivity.CLMST.perfectoidIdeal_TorInput_iff_of_isPullback

noncomputable section
universe u
open SerrePositivity CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

-- An actual quotient square has a potentially nonzero cokernel, killed by J.
theorem audit_actual_quotient_pullback_annihilator
    (R : Type u) [CommRing R] (J : Ideal R) (a : R) (ha : a ∈ J) :
    (∀ x : J.subtype.ker, a • x = 0) ∧
    (∀ y : R ⧸ J.subtype.range, a • y = 0) := by
  let Z := Fin 0 → R
  let f : J →ₗ[R] R := J.subtype
  let l : J →ₗ[R] Z := 0
  let r : R →ₗ[R] R ⧸ J := J.mkQ
  let b : Z →ₗ[R] R ⧸ J := 0
  have hPB : IsPullback (↾f : (J : Type u) ⟶ R) (↾l : (J : Type u) ⟶ Z)
      (↾r : R ⟶ R ⧸ J) (↾b : Z ⟶ R ⧸ J) := by
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · ext x
      exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property
    · intro x y h
      exact Subtype.ext h.1
    · intro x y h
      refine ⟨⟨x, Ideal.Quotient.eq_zero_iff_mem.mp h⟩, rfl, ?_⟩
      exact Subsingleton.elim _ _
  apply linearMap_ker_coker_annihilated_of_type_isPullback f l r b hPB a
  · intro x
    exact Subsingleton.elim _ _
  · intro x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right z ha)

-- A concrete polynomial pullback has an actually nonzero cokernel when C is nonzero.
-- The original perfectoid ideal still annihilates that cokernel.
theorem audit_polynomial_pullback_original_ideal
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0) :
    let r : (Polynomial C) →ₐ[R] (Polynomial C) := AlgHom.id R (Polynomial C)
    let b : C →ₐ[R] (Polynomial C) := IsScalarTower.toAlgHom R C (Polynomial C)
    let f : r.pullback b →ₗ[R] (Polynomial C) := (AlgHom.pullbackFst r b).toLinearMap
    (∀ s ∈ perfectoidIdeal R p hR g, ∀ x : f.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR g, ∀ y : (Polynomial C) ⧸ f.range, s • y = 0) := by
  exact perfectoidIdeal_ker_coker_annihilated_pullbackFst hR _ _ hC g hg

theorem audit_polynomial_pullback_X_nonzero
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] [Nontrivial C] :
    let r : (Polynomial C) →ₐ[R] (Polynomial C) := AlgHom.id R (Polynomial C)
    let b : C →ₐ[R] (Polynomial C) := IsScalarTower.toAlgHom R C (Polynomial C)
    let f : r.pullback b →ₗ[R] (Polynomial C) := (AlgHom.pullbackFst r b).toLinearMap
    f.range.mkQ (Polynomial.X : (Polynomial C)) ≠ 0 := by
  let r : (Polynomial C) →ₐ[R] (Polynomial C) := AlgHom.id R (Polynomial C)
  let b : C →ₐ[R] (Polynomial C) := IsScalarTower.toAlgHom R C (Polynomial C)
  change (AlgHom.pullbackFst r b).toLinearMap.range.mkQ (Polynomial.X : Polynomial C) ≠ 0
  intro h
  obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero
    (AlgHom.pullbackFst r b).toLinearMap.range).mp h
  have he : Polynomial.X = Polynomial.C x.val.2 := hx.symm.trans x.property
  have hc := congrArg (fun f : (Polynomial C) => f.coeff 1) he
  exact one_ne_zero (by simpa only [Polynomial.coeff_X_one, Polynomial.coeff_C_succ] using hc)

assert_no_sorry audit_actual_quotient_pullback_annihilator
assert_no_sorry audit_polynomial_pullback_original_ideal
assert_no_sorry audit_polynomial_pullback_X_nonzero
#print axioms audit_actual_quotient_pullback_annihilator
#print axioms audit_polynomial_pullback_original_ideal
#print axioms audit_polynomial_pullback_X_nonzero
