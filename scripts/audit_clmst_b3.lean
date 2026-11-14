import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.Perfectoidization
import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
import SerrePositivity.BhattScholze.PerfectoidIdeal.Powers
import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
import SerrePositivity.BhattScholze.PerfectoidIdeal.Roots
import SerrePositivity.CLMST.CyclicLengthBound
import Mathlib.Util.PrintSorries
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

assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.algebraMap_quotientPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.algebraMap_base_quotientPerfectoidization
assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.quotientPerfectoidization_subsingleton
assert_no_sorry SerrePositivity.BhattScholze.Semiperfectoid.quotientPerfectoidization_natCast_eq_zero

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
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal
assert_no_sorry SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal_eq_top_of_isUnit
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mono
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal_le_of_mem
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal_p_pow_eq
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mul_unit_eq
assert_no_sorry SerrePositivity.pTorsionIdeal
assert_no_sorry SerrePositivity.mem_pTorsionIdeal
assert_no_sorry SerrePositivity.pTorsionQuotient_isAdicComplete
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_isAdicComplete
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_p_mul_injective
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.pTorsionQuotient_root_mul_injective
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.surjective_pow_mod_p_quotient
assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid
assert_no_sorry SerrePositivity.mem_kernel_comp_quotient_of_pow_mem_span
assert_no_sorry SerrePositivity.BhattScholze.perfectoidQuotient
assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdealQuotientEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectoidIdealQuotientEquiv_mk
assert_no_sorry SerrePositivity.BhattScholze.mem_perfectoidIdeal_of_pow_mem_span_of_reduced
assert_no_sorry SerrePositivity.BhattScholze.perfectoidQuotient_p_isReduced
assert_no_sorry SerrePositivity.Section2.completedTowerRoot
assert_no_sorry SerrePositivity.Section2.completedTowerRoot_pow
assert_no_sorry SerrePositivity.Section2.completedTowerRoot_succ_pow
assert_no_sorry SerrePositivity.Section2.completedTowerRoot_zero
assert_no_sorry SerrePositivity.Section2.completedTowerRoot_pow_of_le
assert_no_sorry SerrePositivity.BhattScholze.completedTowerRoot_mem_perfectoidIdeal_p_of_reduced
assert_no_sorry SerrePositivity.BhattScholze.completedTowerRoot_mem_perfectoidIdeal_p
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

-- C2-4: all elementary cyclic components remain sorry-free.
assert_no_sorry SerrePositivity.CLMST.completedTowerCyclicQuotient_p_regular_and_complete
assert_no_sorry SerrePositivity.CLMST.toPerfectoidization_cyclic_surjective_of_not_dvd
assert_no_sorry SerrePositivity.CLMST.cyclic_length_eq_zero_of_not_dvd
assert_no_sorry SerrePositivity.CLMST.cyclic_length_eq_zero
assert_no_sorry SerrePositivity.CLMST.completedLength_eq_zero_of_perfectoidIdeal_annihilates
assert_no_sorry SerrePositivity.CLMST.completedLength_eq_of_perfectoid_mod_almost_iso
assert_no_sorry SerrePositivity.CLMST.exists_cyclic_root_stage_length_estimate
assert_no_sorry SerrePositivity.CLMST.exists_stage_root_normalized_bound
assert_no_sorry SerrePositivity.CLMST.exists_completed_cyclic_div_pow_bound_of_surjective
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_first_eq_zero_of_surjective
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_pow_eq_zero_of_surjective
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_pow_eq_zero_of_witt_of_surjective
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_pow_eq_of_p_factor
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_p_eq_zero_of_reduced
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_p_eq_zero
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_p_power_unit_eq_zero
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_fin_one_eq_zero
assert_no_sorry SerrePositivity.CLMST.exists_p_power_factor_of_nonzero
assert_no_sorry SerrePositivity.CLMST.exists_p_power_unit_of_fin_one
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_le_of_p_power_factor
assert_no_sorry SerrePositivity.CLMST.completedLength_cyclic_unit_eq_zero


-- C2-5: inspect proof constants, not merely the source imports.
meta section
open Lean Elab Command
private partial def checkDependencies (todo : List Name) (visited : NameSet)
    (allowed : List Name) (forbidden : List Name) : CoreM NameSet := do
  match todo with
  | [] => return visited
  | n :: todo =>
    if visited.contains n then return ← checkDependencies todo visited allowed forbidden
    if forbidden.contains n then throwError "Forbidden dependency: {n}"
    let visited := visited.insert n
    let some info := (← getEnv).find? n
      | return ← checkDependencies todo visited allowed forbidden
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx && !allowed.contains n then
      throwError "Unapproved sorry in {n}"
    checkDependencies (deps.toList ++ todo) visited allowed forbidden

elab "assert_cyclic_B3_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.toPerfectoidization_cyclic_surjective_of_not_dvd,
    ``SerrePositivity.CLMST.cyclic_length_eq_zero_of_not_dvd,
    ``SerrePositivity.CLMST.cyclic_length_eq_zero,
    ``SerrePositivity.CLMST.completedLength_eq_zero_of_perfectoidIdeal_annihilates]
  let allowed : List Name := []
  let forbidden := [`SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral,
    `SerrePositivity.BhattScholze.exists_perfectoidization_of_finite,
    `SerrePositivity.Perfectoidization, `SerrePositivity.toPerfectoidization,
    `SerrePositivity.BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotient]
  let _seen ← liftCoreM <| checkDependencies roots {} allowed forbidden
  logInfo "Cyclic proof paths: sorry-free; old B-I and B-S inputs absent; Andre (Thm 7.14) is proved."

elab "assert_almost_B3_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.completedLength_eq_of_perfectoid_mod_almost_iso]
  let allowed : List Name := []
  let forbidden := [`SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral,
    `SerrePositivity.BhattScholze.exists_perfectoidization_of_finite,
    `SerrePositivity.Perfectoidization, `SerrePositivity.toPerfectoidization,
    `SerrePositivity.BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotient]
  let _seen ← liftCoreM <| checkDependencies roots {} allowed forbidden
  logInfo "Almost length comparison: sorry-free; old B-I and B-S inputs absent; Andre (Thm 7.14) is proved; B-R is proved."
end

assert_cyclic_B3_dependencies
assert_almost_B3_dependencies

assert_no_sorry SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent
