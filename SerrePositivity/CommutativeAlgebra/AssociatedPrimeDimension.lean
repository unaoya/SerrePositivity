module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Regular

/-! # Dimension and nontriviality of associated prime quotients

An associated prime gives an injection of its ring quotient into the module.
For a sequence quotient, its existence also excludes the zero quotient and turns
a weakly regular sequence into a regular sequence.
-/

@[expose] public section

universe u

namespace SerrePositivity.AssociatedPrimeDimension

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The ring quotient of an associated prime has dimension at most the module support. -/
theorem ringKrullDim_quotient_le_supportDim [IsNoetherianRing R] {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p) ≤ Module.supportDim R M := by
  obtain ⟨_, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap p M).mp hp
  rw [← Module.supportDim_quotient_eq_ringKrullDim]
  exact Module.supportDim_le_of_injective f hf

/-- Every associated prime of a ring quotient contains the quotient ideal. -/
theorem le_of_mem_associatedPrimes_quotient (J : Ideal R) {p : Ideal R}
    (hp : p ∈ associatedPrimes R (R ⧸ J)) : J ≤ p := by
  have h := (show IsAssociatedPrime p (R ⧸ J) from hp).annihilator_le
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using h

/-- A weakly regular sequence with an associated prime in its final quotient is regular. -/
theorem isRegular_of_isWeaklyRegular_of_mem_associatedPrimes (rs : List R)
    (hrs : RingTheory.Sequence.IsWeaklyRegular R rs) {p : Ideal R}
    (hp : p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    RingTheory.Sequence.IsRegular R rs := by
  have htop : Ideal.ofList rs ≠ ⊤ :=
    ne_top_of_le_ne_top (show IsAssociatedPrime p (R ⧸ Ideal.ofList rs) from hp).isPrime.ne_top
      (le_of_mem_associatedPrimes_quotient (Ideal.ofList rs) hp)
  exact ⟨hrs, by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using htop.symm⟩

end SerrePositivity.AssociatedPrimeDimension
