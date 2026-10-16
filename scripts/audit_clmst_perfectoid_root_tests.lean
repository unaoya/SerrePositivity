import SerrePositivity.CLMST.PerfectoidIdealTorRoots
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.perfectoidIdeal_eq_compatibleRootCompletion_kernel
assert_no_sorry SerrePositivity.perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow
assert_no_sorry SerrePositivity.compatibleRootIdeal_le_perfectoidIdeal
assert_no_sorry SerrePositivity.perfectoidIdeal_sup_p_pow_eq_compatibleRootIdeal
assert_no_sorry SerrePositivity.perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal
assert_no_sorry SerrePositivity.perfectoidIdeal_le_iff_compatible_roots
assert_no_sorry SerrePositivity.perfectoidIdeal_annihilates_iff_compatible_roots
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_iff_compatible_roots
#print axioms SerrePositivity.perfectoidIdeal_eq_compatibleRootCompletion_kernel
#print axioms SerrePositivity.perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow
#print axioms SerrePositivity.compatibleRootIdeal_le_perfectoidIdeal
#print axioms SerrePositivity.perfectoidIdeal_sup_p_pow_eq_compatibleRootIdeal
#print axioms SerrePositivity.perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal
#print axioms SerrePositivity.perfectoidIdeal_le_iff_compatible_roots
#print axioms SerrePositivity.perfectoidIdeal_annihilates_iff_compatible_roots
#print axioms SerrePositivity.CLMST.perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_iff_compatible_roots

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST CategoryTheory
set_option backward.isDefEq.respectTransparency false

-- The original g and the actual quotient R/p^k retain the span of the specified root images.
theorem audit_original_parameter_mod_power_root_span
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (g : R) (ρ : ℕ → R) (hρ0 : ρ 0 = g) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (k : ℕ) :
    (perfectoidIdeal R p hR g).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) =
      Ideal.span (Set.range (fun n => Ideal.Quotient.mk (Ideal.span {(p : R) ^ k}) (ρ n))) := by
  rw [← hρ0, perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal R p hR ρ hρ]
  rw [compatibleRootIdeal, Ideal.map_span]
  rw [← Set.range_comp]
  rfl

-- The entire original input, over arbitrary power-torsion modules, follows from root tests.
theorem audit_full_original_tor_input_from_roots
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (g : R) (ρ : ℕ → R) (hρ0 : ρ 0 = g) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroots : ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ n,
        torCoefficientScalarEndomorphism C N i (algebraMap R C (ρ n)) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  have h := (perfectoidIdeal_powerTorsionTorInput_iff_compatible_roots R p hR ρ hρ C).mpr hroots
  simpa only [hρ0] using h

-- Changing the chosen root sequence leaves the actual quotient image ideal unchanged.
theorem audit_root_sequence_choice_independence
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ σ : ℕ → R) (h0 : ρ 0 = σ 0)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (hσ : ∀ n, σ (n + 1) ^ p = σ n) (k : ℕ) :
    (compatibleRootIdeal ρ).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) =
      (compatibleRootIdeal σ).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) := by
  rw [← perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal R p hR ρ hρ,
    ← perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal R p hR σ hσ, h0]

assert_no_sorry audit_original_parameter_mod_power_root_span
assert_no_sorry audit_full_original_tor_input_from_roots
assert_no_sorry audit_root_sequence_choice_independence
#print axioms audit_original_parameter_mod_power_root_span
#print axioms audit_full_original_tor_input_from_roots
#print axioms audit_root_sequence_choice_independence
