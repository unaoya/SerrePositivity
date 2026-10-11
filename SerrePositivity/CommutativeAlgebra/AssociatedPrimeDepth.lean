module

public import SerrePositivity.CommutativeAlgebra.PrimeQuotientRegular
public import SerrePositivity.CommutativeAlgebra.AssociatedPrimeQuotient
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Depth bounded by the dimension of an associated-prime quotient

Passing along a regular sequence sends an associated prime to a strictly larger
associated prime of the scalar quotient. Strict inclusion lowers quotient dimension,
which bounds both the sequence length and the depth of the module.
-/

@[expose] public section

universe u

namespace SerrePositivity

open IsLocalRing RingTheory.Sequence

/-- Strict inclusion of prime ideals decreases quotient dimension by at least one. -/
theorem ringKrullDim_quotient_succ_le_of_lt
    {R : Type u} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p < q) : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxq, hxp⟩ := Set.exists_of_ssubset
    (show (p : Set R) ⊂ q from hpq)
  apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
    (Ideal.Quotient.factor_surjective hpq.le)
    (r := Ideal.Quotient.mk p x)
  · apply mem_nonZeroDivisors_of_ne_zero
    exact fun hx => hxp ((Ideal.Quotient.eq_zero_iff_mem).mp hx)
  · change Ideal.Quotient.mk q x = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxq

/-- The induction deriving the sequence length bound from the associated-prime
transition for quotienting by a regular element. -/
theorem length_isWeaklyRegular_le_dim_associatedPrime_of_transition
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hstep : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
      {p : Ideal R}, p ∈ associatedPrimes R M → ∀ (x : R),
      x ∈ maximalIdeal R → IsSMulRegular M x →
      ∃ q : Ideal R, q ∈ associatedPrimes R (QuotSMulTop x M) ∧ p < q)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : IsWeaklyRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction rs generalizing M p with
  | nil =>
    let : p.IsPrime := hp.isPrime
    simpa only [List.length_nil, Nat.cast_zero] using
      (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p))
  | cons x rs ih =>
    obtain ⟨hxreg, htail⟩ := (isWeaklyRegular_cons_iff M x rs).mp hrs
    obtain ⟨q, hq, hpq⟩ := hstep M hp x (hmem x List.mem_cons_self) hxreg
    let : p.IsPrime := hp.isPrime
    let : q.IsPrime := hq.isPrime
    have htailmem : ∀ r ∈ rs, r ∈ maximalIdeal R :=
      fun r hr => hmem r (List.mem_cons_of_mem _ hr)
    have hlen := ih (M := QuotSMulTop x M) htail htailmem hq
    calc
      ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := add_le_add hlen le_rfl
      _ ≤ ringKrullDim (R ⧸ p) := ringKrullDim_quotient_succ_le_of_lt hpq

/-- A regular sequence contained in the maximal ideal has length at most the
dimension of every associated-prime quotient of the module. -/
theorem length_isWeaklyRegular_le_dim_associatedPrime
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : IsWeaklyRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  apply length_isWeaklyRegular_le_dim_associatedPrime_of_transition ?_ rs hrs hmem hp
  intro N _ _ _ q hq x hx hreg
  exact exists_associatedPrime_quotSMulTop_gt hq hx hreg

/-- A module admitting an associated prime is nonzero. -/
theorem nontrivial_of_mem_associatedPrimes
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) : Nontrivial M := by
  rcases subsingleton_or_nontrivial M with h | h
  · let : Subsingleton M := h
    exact False.elim (not_isAssociatedPrime_of_subsingleton hp)
  · exact h

/-- Depth is at most the dimension of any associated-prime quotient. The
associated-prime hypothesis itself ensures that the module is nonzero. -/
theorem depth_le_dim_quotient_of_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (IsLocalRing.depth M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  let : p.IsPrime := hp.isPrime
  let : Nontrivial M := nontrivial_of_mem_associatedPrimes hp
  have hdnonbot : ringKrullDim (R ⧸ p) ≠ ⊥ := by
    intro h
    have hzero := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
    simp [h] at hzero
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hdnonbot
  rw [← hd]
  apply WithBot.coe_le_coe.mpr
  rw [IsLocalRing.depth_eq_sSup_length_isRegular]
  apply sSup_le
  rintro n ⟨rs, hrs, hmem, rfl⟩
  have hlen := length_isWeaklyRegular_le_dim_associatedPrime rs hrs.1 hmem hp
  rw [← hd] at hlen
  exact_mod_cast hlen

end SerrePositivity
