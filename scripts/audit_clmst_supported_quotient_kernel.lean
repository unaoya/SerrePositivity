import SerrePositivity.BhattScholze.PerfectoidizationSupportedQuotientKernel
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff
assert_no_sorry SerrePositivity.perfectoidIdeal_le_iff_compatible_roots_of_quotient_isHausdorff
assert_no_sorry SerrePositivity.IsPerfectoidization.map_kernel_roots_of_surjective_supported_kernel_of_injective_aic
assert_no_sorry SerrePositivity.IsPerfectoidization.map_kernel_roots_of_surjective_supported_kernel_of_aic
#print axioms SerrePositivity.algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff
#print axioms SerrePositivity.perfectoidIdeal_le_iff_compatible_roots_of_quotient_isHausdorff
#print axioms SerrePositivity.IsPerfectoidization.map_kernel_roots_of_surjective_supported_kernel_of_injective_aic
#print axioms SerrePositivity.IsPerfectoidization.map_kernel_roots_of_surjective_supported_kernel_of_aic
#print axioms SerrePositivity.BhattScholze.perfectoidization_map_kernel_roots_of_surjective_supported_kernel
#print axioms SerrePositivity.BhattScholze.perfectoidization_map_kernel_ideal_of_surjective_supported_kernel
#print axioms SerrePositivity.BhattScholze.perfectoidization_map_kernel_originalIdeal_of_surjective_supported_kernel

noncomputable section
universe u
open SerrePositivity SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false

theorem audit_supported_kernel_identity_perfectoidization
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsPerfectoidization p (RingHom.id S) := by
  refine ⟨hS, ?_⟩
  intro T _ _hT k
  refine ⟨k, RingHom.comp_id k, ?_⟩
  intro l hl
  simpa only [RingHom.comp_id] using hl

-- An actual B3 quotient supplies a nontrivial comparison test without André when S is AIC.
theorem audit_aic_b3_annihilator_kernel_roots
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    (hS : IsIntegralPerfectoid S p) (hAIC : IsAbsolutelyIntegrallyClosed S)
    (ρ : ℕ → S) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∀ n, ∀ x : S,
      toQuotientPerfectoidization S (Ideal.span {ρ 0}).annihilator p hS
        (Ideal.Quotient.mk _ x) = 0 → ρ n * x = 0 := by
  let J := (Ideal.span {ρ 0}).annihilator
  let q := Ideal.Quotient.mk J
  let hg := isPerfectoidization_toQuotientPerfectoidization S J p hS
  let hf := audit_supported_kernel_identity_perfectoidization S p hS
  have hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0 := by
    intro a ha
    have hm : a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp ha
    have he := (Submodule.mem_annihilator_span_singleton (ρ 0) a).mp hm
    exact ⟨1, by simpa only [pow_one, smul_eq_mul, mul_comm] using he⟩
  have h := hf.map_kernel_roots_of_surjective_supported_kernel_of_aic hg q
    Ideal.Quotient.mk_surjective hAIC ρ hρ hk
  have he : IsPerfectoidization.map hf hg q =
      (toQuotientPerfectoidization S J p hS).comp q := by
    simpa only [RingHom.comp_id] using IsPerfectoidization.map_comp hf hg q
  rw [he] at h
  exact h

-- Every original R scalar acts through the specified R → S map on the actual B3 target kernel.
theorem audit_original_base_b3_annihilator_kernel
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p) (α : R →+* S)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∀ s ∈ perfectoidIdeal R p hR (ρ 0), ∀ x : S,
      toQuotientPerfectoidization S (Ideal.span {α (ρ 0)}).annihilator p hS
        (Ideal.Quotient.mk _ x) = 0 → α s * x = 0 := by
  let J := (Ideal.span {α (ρ 0)}).annihilator
  let q := Ideal.Quotient.mk J
  let hg := isPerfectoidization_toQuotientPerfectoidization S J p hS
  let hf := audit_supported_kernel_identity_perfectoidization S p hS
  have hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, α (ρ 0) ^ N * a = 0 := by
    intro a ha
    have hm : a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp ha
    have he := (Submodule.mem_annihilator_span_singleton (α (ρ 0)) a).mp hm
    exact ⟨1, by simpa only [pow_one, smul_eq_mul, mul_comm] using he⟩
  have h := perfectoidization_map_kernel_originalIdeal_of_surjective_supported_kernel
    R hR α hf hg q Ideal.Quotient.mk_surjective ρ hρ hk
  have he : IsPerfectoidization.map hf hg q =
      (toQuotientPerfectoidization S J p hS).comp q := by
    simpa only [RingHom.comp_id] using IsPerfectoidization.map_comp hf hg q
  rw [he] at h
  exact h

assert_no_sorry audit_supported_kernel_identity_perfectoidization
assert_no_sorry audit_aic_b3_annihilator_kernel_roots
#print axioms audit_supported_kernel_identity_perfectoidization
#print axioms audit_aic_b3_annihilator_kernel_roots
#print axioms audit_original_base_b3_annihilator_kernel

meta section
open Lean Elab Command
private partial def checkSupportedKernelDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkSupportedKernelDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkSupportedKernelDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed then
      throwError "Unapproved sorry in supported quotient kernel: {n}"
    checkSupportedKernelDependencies (deps.toList ++ rest) seen

elab "assert_supported_kernel_dependencies" : command => do
  let roots :=
    [``SerrePositivity.BhattScholze.perfectoidization_map_kernel_roots_of_surjective_supported_kernel,
     ``SerrePositivity.BhattScholze.perfectoidization_map_kernel_ideal_of_surjective_supported_kernel,
     ``SerrePositivity.BhattScholze.perfectoidization_map_kernel_originalIdeal_of_surjective_supported_kernel,
     ``audit_original_base_b3_annihilator_kernel]
  let seen ← liftCoreM <| checkSupportedKernelDependencies roots {}
  unless seen.contains
      ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed do
    throwError "Expected existing BS Theorem 7.14 dependency is missing"
  logInfo "Supported quotient kernel: only existing BS Theorem 7.14 is permitted."
end

assert_supported_kernel_dependencies
