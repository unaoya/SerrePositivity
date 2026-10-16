import SerrePositivity.CommutativeAlgebra.FiniteFreeScalarFactorization
import SerrePositivity.CommutativeAlgebra.IdempotentImageAnnihilator
import SerrePositivity.HomologicalAlgebra.TorFiniteFreeComparisonAnnihilator
import SerrePositivity.CLMST.PerfectoidIdealTorComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_finiteFree_scalar_lift
assert_no_sorry SerrePositivity.exists_scalar_factorization_through_finiteFree
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_of_finiteFree_comparison
assert_no_sorry SerrePositivity.torCoefficientScalar_algebraMap_eq_zero_of_annihilates
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_of_finiteFree_ideal_square
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_of_finiteFree_almost_comparison
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_finiteFree_comparison

#print axioms SerrePositivity.exists_finiteFree_scalar_lift
#print axioms SerrePositivity.exists_scalar_factorization_through_finiteFree
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_of_finiteFree_comparison
#print axioms SerrePositivity.torCoefficientScalar_algebraMap_eq_zero_of_annihilates
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_of_finiteFree_ideal_square
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_of_finiteFree_almost_comparison
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_finiteFree_comparison

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.CLMST

theorem audit_torsion_source_finiteFree_factorization
    (R : Type u) [CommRing R] (d : R) :
    ∃ v : (Fin 0 → R) →ₗ[R] (R ⧸ Ideal.span {d}),
      v.comp (0 : (R ⧸ Ideal.span {d}) →ₗ[R] (Fin 0 → R)) =
        (1 * d) • LinearMap.id := by
  apply exists_scalar_factorization_through_finiteFree 0 0 1 d
  · intro y
    exact Subsingleton.elim _ _
  · intro x
    apply Subtype.ext
    change d • (x : R ⧸ Ideal.span {d}) = 0
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk (Ideal.span {d}) d * (x : R ⧸ Ideal.span {d}) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self d), zero_mul]

theorem audit_perfectoid_finiteProduct_powerTorsion_Tor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (r : ℕ)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ perfectoidIdeal R p hR g) :
    torCoefficientScalarEndomorphism (Fin r → R) N i
      (algebraMap R (Fin r → R) s) = 0 := by
  let C := Fin r → R
  let f : C →ₗ[R] C := LinearMap.id
  letI : Subsingleton f.ker := by
    change Subsingleton (LinearMap.id (R := R) (M := C)).ker
    rw [LinearMap.ker_id]
    infer_instance
  letI : Subsingleton (C ⧸ f.range) := by
    change Subsingleton (C ⧸ (LinearMap.id (R := R) (M := C)).range)
    rw [LinearMap.range_id]
    infer_instance
  exact perfectoidIdeal_powerTorsionTorInput_of_finiteFree_comparison R p hR g C r f
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)
    N k hN i hi s hs

assert_no_sorry audit_torsion_source_finiteFree_factorization
assert_no_sorry audit_perfectoid_finiteProduct_powerTorsion_Tor
#print axioms audit_torsion_source_finiteFree_factorization
#print axioms audit_perfectoid_finiteProduct_powerTorsion_Tor
