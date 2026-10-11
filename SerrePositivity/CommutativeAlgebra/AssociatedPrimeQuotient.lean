module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Associated primes after quotienting by a regular element

Over a Noetherian local ring, every associated prime of a finite module lies
strictly below an associated prime after killing a regular element in the
maximal ideal. Krull intersection provides a primitive representative of the
associated element modulo that regular element.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace SerrePositivity

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A nonzero element of a finite module has finite order for a scalar in the
maximal ideal. Divide by the largest possible power to obtain an element not
in `xM`. Regularity of `x` is not needed for this existence statement. -/
lemma exists_pow_smul_not_mem_smul_top (x : R) (a : M)
    (hx : x ∈ maximalIdeal R) (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ b : M, a = x ^ n • b ∧ b ∉ x • (⊤ : Submodule R M) := by
  classical
  have hI : Ideal.span {x} ≠ (⊤ : Ideal R) :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      (Ideal.span_le.mpr (by simpa))
  have h : ∃ n : ℕ, ¬ ∃ b : M, a = x ^ n • b := by
    by_contra! h
    apply ha
    have hall : a ∈ (⨅ n : ℕ, (Ideal.span {x}) ^ n • ⊤ : Submodule R M) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      obtain ⟨b, rfl⟩ := h n
      exact Submodule.smul_mem_pointwise_smul b (x ^ n) ⊤ Submodule.mem_top
    rwa [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ hI, Submodule.mem_bot] at hall
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.find h ≠ 0 by
    intro heq
    have hf := Nat.find_spec h
    rw [heq] at hf
    exact hf ⟨a, by simp⟩)
  have hd : ∃ b : M, a = x ^ n • b := by
    by_contra hd
    have hmin := Nat.find_min' h hd
    omega
  obtain ⟨b, hab⟩ := hd
  refine ⟨n, b, hab, ?_⟩
  intro hb
  obtain ⟨c, _, hcb⟩ := (Submodule.mem_smul_pointwise_iff_exists b x ⊤).mp hb
  apply Nat.find_spec h
  rw [hn]
  refine ⟨c, ?_⟩
  rw [pow_succ, mul_smul, hcb]
  exact hab

/-- Every associated prime strictly grows along the quotient by a regular
element in the maximal ideal. -/
theorem exists_associatedPrime_quotSMulTop_gt {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) {x : R} (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    ∃ q : Ideal R, q ∈ associatedPrimes R (QuotSMulTop x M) ∧ p < q := by
  obtain ⟨hpp, a, hpa⟩ := isAssociatedPrime_iff.mp hp
  have ha : a ≠ 0 := by
    intro ha
    apply hpp.ne_top
    simp [hpa, ha]
  have hxp : x ∉ p := by
    intro hxmem
    rw [hpa, Submodule.mem_colon_singleton, Submodule.mem_bot] at hxmem
    exact ha (hreg.right_eq_zero_of_smul hxmem)
  obtain ⟨n, b, hab, hb⟩ := exists_pow_smul_not_mem_smul_top x a hx ha
  have hpb : p = (⊥ : Submodule R M).colon {b} := by
    ext r
    rw [hpa, Submodule.mem_colon_singleton, Submodule.mem_colon_singleton,
      Submodule.mem_bot, Submodule.mem_bot, hab, smul_comm r (x ^ n) b]
    constructor
    · exact (hreg.pow n).right_eq_zero_of_smul
    · intro hr
      rw [hr, smul_zero]
  let f : M →ₗ[R] QuotSMulTop x M := (x • (⊤ : Submodule R M)).mkQ
  have hfb : f b ≠ 0 := by
    intro hzero
    apply hb
    exact (Submodule.Quotient.mk_eq_zero (p := x • (⊤ : Submodule R M)) (x := b)).mp hzero
  obtain ⟨q, hq, hqann⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R (f b) hfb
  have hpq : p ≤ q := by
    apply le_trans _ hqann
    intro r hr
    rw [hpb, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← f.map_smul, hr, map_zero]
  have hxq : x ∈ q := by
    apply hqann
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change (Submodule.Quotient.mk (x • b) : QuotSMulTop x M) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul b x ⊤ Submodule.mem_top
  refine ⟨q, hq, lt_of_le_of_ne hpq ?_⟩
  intro heq
  exact hxp (heq.symm ▸ hxq)

end SerrePositivity
