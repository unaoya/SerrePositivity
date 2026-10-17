import SerrePositivity.CLMST.PerfectoidIdealTorCover
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.perfectoidIdeal_le_ker_of_eq_zero
assert_no_sorry SerrePositivity.perfectoidIdeal_le_compatibleRootFamilyIdeal_sup_p_pow
assert_no_sorry SerrePositivity.perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover
assert_no_sorry SerrePositivity.perfectoidIdeal_annihilates_of_rooted_cover
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_torCoefficientScalar_eq_zero_of_rooted_cover
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_cover
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover
#print axioms SerrePositivity.perfectoidIdeal_le_ker_of_eq_zero
#print axioms SerrePositivity.perfectoidIdeal_le_compatibleRootFamilyIdeal_sup_p_pow
#print axioms SerrePositivity.perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover
#print axioms SerrePositivity.perfectoidIdeal_annihilates_of_rooted_cover
#print axioms SerrePositivity.CLMST.perfectoidIdeal_torCoefficientScalar_eq_zero_of_rooted_cover
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_cover
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover

noncomputable section
universe u
open SerrePositivity
set_option backward.isDefEq.respectTransparency false

-- All original almost scalars vanish in the actual universal test quotient.
theorem audit_rooted_cover_canonical_quotient
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ) (k : ℕ)
    (a : R) (ha : a ∈ perfectoidIdeal R p hR g) :
    Ideal.Quotient.mk ((⨆ s, perfectoidIdeal R p hR (ρ s 0)) ⊔
      Ideal.span {(p : R) ^ k}) a = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover R p hR ρ hρ g N hcover k ha)

-- Gluing two different local generators controls their sum, without roots of the sum.
theorem audit_two_generator_almost_annihilation
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ULift.{u} (Fin 2) → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (hM : ∀ x : M, (p : R) ^ k • x = 0)
    (hlocal : ∀ s, ∀ a ∈ perfectoidIdeal R p hR (ρ s 0), ∀ x : M, a • x = 0) :
    ∀ a ∈ perfectoidIdeal R p hR (ρ ⟨0⟩ 0 + ρ ⟨1⟩ 0), ∀ x : M, a • x = 0 := by
  apply perfectoidIdeal_annihilates_of_rooted_cover R p hR ρ hρ
    (ρ ⟨0⟩ 0 + ρ ⟨1⟩ 0) 1 _ M k hM hlocal
  rw [pow_one]
  apply Ideal.add_mem
  · exact Ideal.mem_span_range_self (x := (⟨0⟩ : ULift.{u} (Fin 2)))
  · exact Ideal.mem_span_range_self (x := (⟨1⟩ : ULift.{u} (Fin 2)))

-- The empty-cover case is valid even for a nilpotent original generator.
theorem audit_empty_rooted_cover
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (g : R) (N : ℕ) (hg : g ^ N = 0)
    (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (hM : ∀ x : M, (p : R) ^ k • x = 0) :
    ∀ a ∈ perfectoidIdeal R p hR g, ∀ x : M, a • x = 0 := by
  let ρ : PEmpty.{u + 1} → ℕ → R := fun s => nomatch s
  apply perfectoidIdeal_annihilates_of_rooted_cover R p hR ρ (fun s => nomatch s)
    g N _ M k hM (fun s => nomatch s)
  rw [hg]
  exact Ideal.zero_mem _

assert_no_sorry audit_rooted_cover_canonical_quotient
assert_no_sorry audit_two_generator_almost_annihilation
assert_no_sorry audit_empty_rooted_cover
#print axioms audit_rooted_cover_canonical_quotient
#print axioms audit_two_generator_almost_annihilation
#print axioms audit_empty_rooted_cover
