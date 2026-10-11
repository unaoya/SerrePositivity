module

public import SerrePositivity.CommutativeAlgebra.ArtinReesGrowth
public import SerrePositivity.CommutativeAlgebra.SamuelModuleProperties
public import SerrePositivity.CommutativeAlgebra.PolynomialGrowth

/-!
# Strict decrease of Samuel degree along regular quotients

Artin–Rees bounds the Samuel function of a regular-element quotient by a backward
finite difference of the original Samuel function. A nonzero finite module whose
Samuel function is bounded by that of the quotient consequently has strictly
smaller Samuel polynomial degree than the original module.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

/-- Transfer an additive inequality between finite extended natural numbers to rational
numbers. This is the numerical passage from length inequalities to polynomial values. -/
theorem toNat_rat_add_le_of_add_le {a b c : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hc : c ≠ ⊤) (h : a + b ≤ c) :
    (a.toNat : ℚ) + (b.toNat : ℚ) ≤ (c.toNat : ℚ) := by
  have hn := ENat.toNat_le_toNat h hc
  rw [ENat.toNat_add ha hb] at hn
  exact_mod_cast hn

variable {R M N : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]

/-- Any nonzero finite module with Samuel function bounded by that of a regular quotient
has strictly lower polynomial degree than the original module. -/
theorem IsSamuelPoly.natDegree_lt_of_le_regular_quotient
    {I : Ideal R} (hI : I.radical = maximalIdeal R) {P Q : ℚ[X]}
    (hP : IsSamuelPoly R I M P) (hQ : IsSamuelPoly R I N Q)
    (x : R) (hx : IsSMulRegular M x)
    (hN : ∀ n : ℕ, samuelFunction R I N n ≤
      samuelFunction R I (QuotSMulTop x M) n) :
    Q.natDegree < P.natDegree := by
  obtain ⟨c, hc, hdiff⟩ := exists_samuelFunction_quotSMulTop_add_le I x hx
  apply PolynomialGrowth.natDegree_lt_of_eventually_eval_add_shift_le
    (hQ.leadingCoeff_pos_of_nontrivial hI) c
  obtain ⟨k, hk⟩ := eventually_atTop.mp hP
  have hPshift : ∀ᶠ n : ℕ in atTop,
      samuelFunction R I M (n - c) ≠ ⊤ ∧
        ((samuelFunction R I M (n - c)).toNat : ℚ) = P.eval ((n - c : ℕ) : ℚ) := by
    apply eventually_atTop.mpr
    refine ⟨k + c, fun n hn => hk (n - c) ?_⟩
    omega
  filter_upwards [hP, hQ, hPshift, eventually_ge_atTop c] with n hnP hnQ hnPc hnc
  rw [← hnQ.2, ← hnPc.2, ← hnP.2]
  apply toNat_rat_add_le_of_add_le hnQ.1 hnPc.1 hnP.1
  exact (add_le_add (hN n) le_rfl).trans (hdiff n hnc)

/-- In particular, a nonzero regular-element quotient has strictly smaller Samuel degree. -/
theorem IsSamuelPoly.natDegree_lt_quotSMulTop
    {I : Ideal R} (hI : I.radical = maximalIdeal R) {P Q : ℚ[X]}
    (hP : IsSamuelPoly R I M P) (x : R) (hx : IsSMulRegular M x)
    [Nontrivial (QuotSMulTop x M)]
    (hQ : IsSamuelPoly R I (QuotSMulTop x M) Q) :
    Q.natDegree < P.natDegree :=
  hP.natDegree_lt_of_le_regular_quotient hI hQ x hx (fun _ => le_rfl)

end SerrePositivity.HilbertSamuel
