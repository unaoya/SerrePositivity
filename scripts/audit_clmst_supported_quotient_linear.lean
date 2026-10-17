import SerrePositivity.BhattScholze.PerfectoidizationSupportedQuotientLinear
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.mapAlgHom
assert_no_sorry SerrePositivity.IsPerfectoidization.mapAlgHom_toRingHom
assert_no_sorry SerrePositivity.IsPerfectoidization.mapAlgHom_comp
#print axioms SerrePositivity.IsPerfectoidization.mapAlgHom
#print axioms SerrePositivity.IsPerfectoidization.mapAlgHom_comp
#print axioms SerrePositivity.BhattScholze.perfectoidization_mapAlgHom_ker_coker_annihilated_of_surjective_supported_kernel

noncomputable section
universe u
open SerrePositivity SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false

-- The actual B3 quotient uses its existing original-base action, not a replacement instance.
theorem audit_b3_annihilator_original_linear_ker_coker
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    let D := QuotientPerfectoidization R (Ideal.span {ρ 0}).annihilator p hR
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ x : (Algebra.linearMap R D).ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ y : D ⧸ (Algebra.linearMap R D).range, s • y = 0) := by
  let J := (Ideal.span {ρ 0}).annihilator
  let Q := R ⧸ J
  let D := QuotientPerfectoidization R J p hR
  let q : R →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  let f : R →ₐ[R] R := AlgHom.id R R
  let g : Q →ₐ[R] D := IsScalarTower.toAlgHom R Q D
  have hf : IsPerfectoidization p f.toRingHom := by
    refine ⟨hR, ?_⟩
    intro T _ _ k
    refine ⟨k, RingHom.comp_id k, ?_⟩
    intro l hl
    change l.comp (RingHom.id R) = k at hl
    simpa only [RingHom.comp_id] using hl
  have hg : IsPerfectoidization p g.toRingHom :=
    isPerfectoidization_toQuotientPerfectoidization R J p hR
  have hk : ∀ a ∈ RingHom.ker q.toRingHom,
      ∃ N : ℕ, (algebraMap R R (ρ 0)) ^ N * a = 0 := by
    intro a ha
    have he := (Submodule.mem_annihilator_span_singleton (ρ 0) a).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    exact ⟨1, by simpa only [Algebra.algebraMap_self, RingHom.id_apply, pow_one, smul_eq_mul, mul_comm] using he⟩
  have h := perfectoidization_mapAlgHom_ker_coker_annihilated_of_surjective_supported_kernel
    hR hf hg q (Ideal.Quotient.mkₐ_surjective R J) ρ hρ hk
  have hm : (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap = Algebra.linearMap R D := by
    apply LinearMap.ext
    intro r
    exact (IsPerfectoidization.mapAlgHom hf hg q).commutes r
  rw [hm] at h
  exact h

#print axioms audit_b3_annihilator_original_linear_ker_coker

meta section
open Lean Elab Command
private partial def checkLinearComparisonDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkLinearComparisonDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkLinearComparisonDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed then
      throwError "Unapproved sorry in actual linear comparison: {n}"
    checkLinearComparisonDependencies (deps.toList ++ rest) seen

elab "assert_linear_comparison_dependencies" : command => do
  let seen ← liftCoreM <| checkLinearComparisonDependencies
    [``SerrePositivity.BhattScholze.perfectoidization_mapAlgHom_ker_coker_annihilated_of_surjective_supported_kernel,
     ``audit_b3_annihilator_original_linear_ker_coker] {}
  unless seen.contains
      ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed do
    throwError "Expected existing BS Theorem 7.14 dependency is missing"
  logInfo "Original linear comparison: only existing BS Theorem 7.14 is permitted."
end

assert_linear_comparison_dependencies
