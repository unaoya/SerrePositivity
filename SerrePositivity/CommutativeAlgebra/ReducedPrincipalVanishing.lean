module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.Operations

/-! # Vanishing on a principal open of a reduced ring

The vanishing ideal is exactly the annihilator of the original scalar.
No regularity, finiteness, or nonzero hypothesis is required.
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- In a reduced ring the ideal vanishing on D(d) is Ann(d). -/
theorem vanishingIdeal_basicOpen_eq_annihilator
    (R : Type u) [CommRing R] [IsReduced R] (d : R) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum R)) =
      (Ideal.span {d}).annihilator := by
  ext x
  rw [PrimeSpectrum.mem_vanishingIdeal, Submodule.mem_annihilator_span_singleton]
  change (∀ P : PrimeSpectrum R, d ∉ P.asIdeal → x ∈ P.asIdeal) ↔ x * d = 0
  constructor
  · intro hx
    have hn : x * d ∈ nilradical R := by
      rw [PrimeSpectrum.nilradical_eq_iInf, Submodule.mem_iInf]
      intro P
      by_cases hd : d ∈ P.asIdeal
      · exact P.asIdeal.mul_mem_left x hd
      · exact P.asIdeal.mul_mem_right d (hx P hd)
    exact (mem_nilradical.mp hn).eq_zero
  · intro hx P hd
    exact (P.isPrime.mem_or_mem (hx ▸ P.asIdeal.zero_mem)).resolve_right hd

end SerrePositivity
