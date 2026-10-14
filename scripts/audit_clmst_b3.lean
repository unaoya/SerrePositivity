import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
import SerrePositivity.BhattScholze.QuotientPerfectoidization
import SerrePositivity.CommutativeAlgebra.PerfectoidIdeal
import SerrePositivity.CommutativeAlgebra.PerfectoidizationMap
import SerrePositivity.CommutativeAlgebra.PerfectoidIdealPowers
import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionQuotient
import SerrePositivity.CLMST.PerfectoidIdealRoots
import SerrePositivity.CLMST.PerfectoidFrobeniusComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.lift
assert_no_sorry SerrePositivity.IsPerfectoidization.lift_comp
assert_no_sorry SerrePositivity.IsPerfectoidization.lift_unique
assert_no_sorry SerrePositivity.IsPerfectoidization.map
assert_no_sorry SerrePositivity.IsPerfectoidization.map_comp
assert_no_sorry SerrePositivity.IsPerfectoidization.map_id
assert_no_sorry SerrePositivity.IsPerfectoidization.map_map
assert_no_sorry SerrePositivity.IsPerfectoidization.exists_equiv
assert_no_sorry SerrePositivity.IsPerfectoidization.surjective_iff
assert_no_sorry SerrePositivity.IsPerfectoidization.ker_eq
assert_no_sorry SerrePositivity.IsPerfectoidization.ker_comp_eq

assert_no_sorry SerrePositivity.QuotientPerfectoidization
assert_no_sorry SerrePositivity.toQuotientPerfectoidization
assert_no_sorry SerrePositivity.isPerfectoidization_toQuotientPerfectoidization
assert_no_sorry SerrePositivity.algebraMap_quotientPerfectoidization
assert_no_sorry SerrePositivity.algebraMap_base_quotientPerfectoidization
assert_no_sorry SerrePositivity.quotientPerfectoidization_subsingleton
assert_no_sorry SerrePositivity.quotientPerfectoidization_natCast_eq_zero

open SerrePositivity

-- Arbitrary ideals, without finiteness or completeness assumptions on the quotient.
example {R : Type} [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    IsScalarTower R (R ⧸ I) (QuotientPerfectoidization R I p hR) := inferInstance

example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    IsPerfectoidization p (toQuotientPerfectoidization R (Ideal.span {0}) p hR) :=
  isPerfectoidization_toQuotientPerfectoidization R _ p hR

example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (hg : IsUnit g) :
    Subsingleton (QuotientPerfectoidization R (Ideal.span {g}) p hR) := by
  let : Subsingleton (R ⧸ Ideal.span {g}) := by
    rw [Ideal.span_singleton_eq_top.mpr hg]
    infer_instance
  exact quotientPerfectoidization_subsingleton R _ p hR

example {R : Type} [CommRing R] [Subsingleton R] (p : ℕ) [Fact p.Prime]
    (I : Ideal R) :
    Subsingleton (QuotientPerfectoidization R I p (Or.inl inferInstance)) :=
  quotientPerfectoidization_subsingleton R I p _

example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    (p : QuotientPerfectoidization R (Ideal.span {(p : R)}) p hR) = 0 :=
  quotientPerfectoidization_natCast_eq_zero R _ p hR (Ideal.mem_span_singleton_self _)

-- C2-3: kernel, roots, Frobenius, and torsion-factor comparisons.
assert_no_sorry SerrePositivity.perfectoidIdeal
assert_no_sorry SerrePositivity.span_le_perfectoidIdeal
assert_no_sorry SerrePositivity.perfectoidIdeal_eq_top_of_isUnit
assert_no_sorry SerrePositivity.perfectoidIdeal_mono
assert_no_sorry SerrePositivity.perfectoidIdeal_le_of_mem
assert_no_sorry SerrePositivity.perfectoidIdeal_p_pow_eq
assert_no_sorry SerrePositivity.perfectoidIdeal_mul_unit_eq
assert_no_sorry SerrePositivity.pTorsionIdeal
assert_no_sorry SerrePositivity.mem_pTorsionIdeal
assert_no_sorry SerrePositivity.pTorsionQuotient_isAdicComplete
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_isAdicComplete
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.exists_unit_p_root_quotient
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_p_mul_injective
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_root_mul_injective
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.surjective_pow_mod_p_quotient
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_perfectoid_of_fontaine_kernel
assert_no_sorry SerrePositivity.perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid
assert_no_sorry SerrePositivity.CLMST.mem_kernel_comp_quotient_of_pow_mem_span
assert_no_sorry SerrePositivity.CLMST.perfectoidQuotient
assert_no_sorry SerrePositivity.CLMST.perfectoidIdealQuotientEquiv
assert_no_sorry SerrePositivity.CLMST.perfectoidIdealQuotientEquiv_mk
assert_no_sorry SerrePositivity.CLMST.mem_perfectoidIdeal_of_pow_mem_span_of_reduced
assert_no_sorry SerrePositivity.CLMST.perfectoidQuotient_p_isReduced
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_pow
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_succ_pow
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_zero
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_pow_of_le
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_mem_perfectoidIdeal_p_of_reduced
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_mem_perfectoidIdeal_p
assert_no_sorry SerrePositivity.CLMST.iterate_pow_apply
assert_no_sorry SerrePositivity.CLMST.exists_root_mod_p_of_surjective
assert_no_sorry SerrePositivity.CLMST.exists_root_mod_p_of_perfectoid
assert_no_sorry SerrePositivity.CLMST.quotientRootFrobenius
assert_no_sorry SerrePositivity.CLMST.quotientRootFrobenius_mk
assert_no_sorry SerrePositivity.CLMST.root_mem_sup_of_quotient_frobenius_injective
assert_no_sorry SerrePositivity.CLMST.quotientRootFrobenius_injective_of_integralPerfectoid
assert_no_sorry SerrePositivity.CLMST.root_mem_sup_of_surjective_perfectoid
assert_no_sorry SerrePositivity.CLMST.root_mem_sup_perfectoidIdeal_of_surjective
assert_no_sorry SerrePositivity.CLMST.exists_completed_root_mem_sup_perfectoidIdeal_of_surjective
assert_no_sorry SerrePositivity.CLMST.pow_sub_mem_of_sub_mem
assert_no_sorry SerrePositivity.CLMST.exists_stage_root_mod_p_of_perfectoid
assert_no_sorry SerrePositivity.CLMST.exists_stage_root_mem_sup_perfectoidIdeal_of_surjective
assert_no_sorry SerrePositivity.CLMST.sub_mem_root_span_of_pow_sub_mem_p

-- The actual ideal now is the kernel of the B3 map, definitionally.
example {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) :
    perfectoidIdeal R p hR g = RingHom.ker
      ((toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
        (Ideal.Quotient.mk (Ideal.span {g}))) := rfl
