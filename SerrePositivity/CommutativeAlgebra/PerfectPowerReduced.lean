module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # A bijective power map of exponent greater than one forces reducedness -/

@[expose] public section
universe u
namespace SerrePositivity

/-- No characteristic or nontriviality hypothesis is needed, including for zero quotients. -/
lemma isReduced_of_perfectPower (R : Type u) [CommRing R] (p : ℕ)
    [PerfectRing R p] (hp : 1 < p) : IsReduced R :=
  (isReduced_iff_pow_one_lt p hp).mpr (by
    intro x hx
    exact (PerfectRing.bijective_frobenius (R := R) (p := p)).injective
      (by simpa only [zero_pow (by omega : p ≠ 0)] using hx))

end SerrePositivity
