module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelPolynomial
public import SerrePositivity.CommutativeAlgebra.PolynomialGrowth
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Comparing Samuel growth for primary ideals

The degree of a Samuel polynomial does not depend on the choice of an ideal whose radical
is the maximal ideal. The proof uses power containment, comparison of quotient lengths,
and polynomial growth. It does not use the Hilbert–Samuel dimension theorem.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

variable (R : Type u) [CommRing R]

/-- A power containment gives a linear change of index in the Samuel length bound. -/
theorem samuelFunction_le_mul_of_pow_le
    (M : Type u) [AddCommGroup M] [Module R M]
    {I J : Ideal R} {c : ℕ} (hJI : J ^ c ≤ I) (n : ℕ) :
    samuelFunction R I M n ≤ samuelFunction R J M (c * n) := by
  have h := samuelFunction_antitone_ideal R M n hJI
  change samuelFunction R I M n ≤ samuelFunction R (J ^ c) M n at h
  rwa [samuelFunction_pow] at h

variable [IsNoetherianRing R] [IsLocalRing R]

/-- The selected Samuel polynomial represents the length function of any finite module over
a Noetherian local ring, for an ideal whose radical is the maximal ideal. -/
theorem isSamuelPoly_poly_of_radical
    (I : Ideal R) (hI : I.radical = maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsSamuelPoly R I M (poly R I M) := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨Q, hQ⟩ := exists_rational_hilbertSeries R I M hI x hx
  obtain ⟨P, hP, _⟩ := exists_isSamuelPoly_of_hilbertSeries R I M hI s Q hQ
  exact isSamuelPoly_poly R ⟨P, hP⟩

/-- A power containment bounds the degree of one Samuel polynomial by the other. -/
theorem natDegree_poly_le_of_pow_le
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) {c : ℕ} (hc : 0 < c) (hJI : J ^ c ≤ I) :
    (poly R I R).natDegree ≤ (poly R J R).natDegree := by
  have hP := isSamuelPoly_poly_of_radical R I hI R
  have hQ := isSamuelPoly_poly_of_radical R J hJ R
  have hQcn : ∀ᶠ n : ℕ in atTop,
      samuelFunction R J R (c * n) ≠ ⊤ ∧
        ((samuelFunction R J R (c * n)).toNat : ℚ) = (poly R J R).eval ((c * n : ℕ) : ℚ) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hQ
    apply eventually_atTop.mpr
    exact ⟨N, fun n hn => hN (c * n) (hn.trans (Nat.le_mul_of_pos_left n hc))⟩
  apply PolynomialGrowth.natDegree_le_of_eventually_eval_affine_le
    (hP.leadingCoeff_pos R hI) c 0
  filter_upwards [hP, hQcn] with n hnI hnJ
  simp only [Nat.add_zero]
  rw [← hnI.2, ← hnJ.2]
  exact_mod_cast ENat.toNat_le_toNat (samuelFunction_le_mul_of_pow_le R R hJI n) hnJ.1

/-- Increasing a primary ideal cannot increase the degree of its Samuel polynomial. -/
theorem natDegree_poly_antitone_of_le
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) (hIJ : I ≤ J) :
    (poly R J R).natDegree ≤ (poly R I R).natDegree :=
  natDegree_poly_le_of_pow_le R J I hJ hI (c := 1) (by decide) (by simpa using hIJ)

/-- Ideals with maximal radical contain positive powers of one another. -/
theorem exists_pos_pow_le_of_radical_eq
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) :
    ∃ c : ℕ, 0 < c ∧ J ^ c ≤ I := by
  have hle : J ≤ I.radical := Ideal.le_radical.trans_eq (hJ.trans hI.symm)
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle J.fg_of_isNoetherianRing
  exact ⟨c + 1, Nat.succ_pos c, (Ideal.pow_le_pow_right (Nat.le_succ c)).trans hc⟩

/-- The Samuel polynomial degree is independent of the ideal with maximal radical. This
comparison is independent of its later identification with Krull dimension. -/
theorem natDegree_poly_eq_of_radical_eq
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) :
    (poly R I R).natDegree = (poly R J R).natDegree := by
  obtain ⟨c, hc, hJI⟩ := exists_pos_pow_le_of_radical_eq R I J hI hJ
  obtain ⟨d, hd, hIJ⟩ := exists_pos_pow_le_of_radical_eq R J I hJ hI
  exact le_antisymm (natDegree_poly_le_of_pow_le R I J hI hJ hc hJI)
    (natDegree_poly_le_of_pow_le R J I hJ hI hd hIJ)

end SerrePositivity.HilbertSamuel
