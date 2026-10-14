module
public import SerrePositivity.CommutativeAlgebra.FlatLocalDimension
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # Height, quotient dimension, and finite numerical bounds -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- The dimension of a prime quotient is the order coheight of its prime. -/
lemma primeQuotientDimension_eq_coheight (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  rw [ringKrullDim,
    Order.krullDim_eq_of_orderIso p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus]
  have hz : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) = Set.Ici p := by
    ext q
    rfl
  rw [hz, ← Order.coheight_eq_krullDim_Ici]

/-- Chains below and above a prime concatenate to give this general dimension bound. -/
lemma primeHeight_add_quotientDimension_le (p : PrimeSpectrum R) :
    (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p.asIdeal) ≤ ringKrullDim R := by
  have : Nonempty (PrimeSpectrum R) := ⟨p⟩
  rw [p.height_eq_orderHeight, primeQuotientDimension_eq_coheight, ← WithBot.coe_add]
  change ((Order.height p + Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤
    Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun q : PrimeSpectrum R =>
    Order.height q + Order.coheight q) p)

/-- Finite-dimensional rings allow the natural-number height to recover the original height. -/
lemma natCast_primeHeight_toNat [FiniteRingKrullDim R] (p : PrimeSpectrum R) :
    (p.asIdeal.height.toNat : ℕ∞) = p.asIdeal.height :=
  ENat.natCast_toNat (Ideal.height_ne_top p.isPrime.ne_top)

/-- A strict inclusion of finite-height primes strictly raises height. -/
lemma primeHeight_strictMono_of_finite (p q : PrimeSpectrum R)
    [p.asIdeal.FiniteHeight] (h : p < q) : p.asIdeal.height < q.asIdeal.height :=
  Ideal.height_strict_mono_of_isPrime h

/-- In a finite-dimensional ring, strict prime inclusion raises the numerical height. -/
lemma primeHeight_toNat_strictMono [FiniteRingKrullDim R] (p q : PrimeSpectrum R)
    (h : p < q) : p.asIdeal.height.toNat < q.asIdeal.height.toNat := by
  have he := primeHeight_strictMono_of_finite p q h
  rw [← natCast_primeHeight_toNat p, ← natCast_primeHeight_toNat q] at he
  exact_mod_cast he

/-- A prime quotient of a finite-dimensional ring remains finite-dimensional. -/
lemma finiteRingKrullDim_primeQuotient [FiniteRingKrullDim R] (p : PrimeSpectrum R) :
    FiniteRingKrullDim (R ⧸ p.asIdeal) := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  refine ⟨?_, ?_⟩
  · rw [primeQuotientDimension_eq_coheight]
    exact WithBot.coe_ne_bot
  · exact (lt_of_le_of_lt (ringKrullDim_quotient_le p.asIdeal) ringKrullDim_lt_top).ne

/-- The height-plus-quotient-dimension bound in natural numbers. -/
lemma primeHeight_toNat_add_quotientDimToNat_le [FiniteRingKrullDim R] (p : PrimeSpectrum R) :
    p.asIdeal.height.toNat + dimToNat (ringKrullDim (R ⧸ p.asIdeal)) ≤
      dimToNat (ringKrullDim R) := by
  have := finiteRingKrullDim_primeQuotient p
  have h := primeHeight_add_quotientDimension_le p
  rw [← natCast_dimToNat_ringKrullDim (R ⧸ p.asIdeal),
    ← natCast_dimToNat_ringKrullDim R, ← natCast_primeHeight_toNat p] at h
  exact_mod_cast h
end SerrePositivity
