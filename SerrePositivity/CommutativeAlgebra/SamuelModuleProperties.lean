module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import Mathlib.RingTheory.Nakayama

/-!
# Positivity and invariance of Samuel functions of modules

Nakayama's lemma shows that the Samuel function of a nonzero finite module over
a local ring is positive in every positive degree. This implies positivity of
the leading coefficient of any polynomial representing that function.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An `R`-linear equivalence identifies the quotients by every ideal power. -/
noncomputable def samuelQuotientEquiv (I : Ideal R) (e : M ≃ₗ[R] N) (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

/-- Samuel functions depend only on the isomorphism class of the module. -/
lemma samuelFunction_eq_of_linearEquiv (I : Ideal R) (e : M ≃ₗ[R] N) (n : ℕ) :
    samuelFunction R I M n = samuelFunction R I N n :=
  (samuelQuotientEquiv I e n).length_eq

/-- A Samuel polynomial remains a Samuel polynomial after a linear equivalence. -/
lemma IsSamuelPoly.of_linearEquiv {I : Ideal R} {P : ℚ[X]}
    (hP : IsSamuelPoly R I M P) (e : M ≃ₗ[R] N) : IsSamuelPoly R I N P := by
  simpa only [IsSamuelPoly, ← samuelFunction_eq_of_linearEquiv I e] using hP

section localModules

variable [IsLocalRing R] [Module.Finite R M] [Nontrivial M]

/-- Nakayama: a proper ideal power cannot generate a nonzero finite module. -/
lemma pow_smul_top_ne_top (I : Ideal R) (hI : I.radical = maximalIdeal R)
    {n : ℕ} (hn : 0 < n) : (I ^ n • ⊤ : Submodule R M) ≠ ⊤ := by
  intro h
  have hrad : I ^ n ≤ Ideal.jacobson (⊥ : Ideal R) :=
    ((Ideal.pow_le_self hn.ne').trans (Ideal.le_radical.trans_eq hI)).trans
      (maximalIdeal_le_jacobson _)
  have hz := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (I ^ n)
    (⊤ : Submodule R M) Module.Finite.fg_top (by rw [h]) hrad
  exact top_ne_bot hz

/-- Positive powers give nonzero quotients, so the Samuel function is positive. -/
lemma samuelFunction_pos_of_nontrivial (I : Ideal R)
    (hI : I.radical = maximalIdeal R) {n : ℕ} (hn : 0 < n) :
    0 < samuelFunction R I M n := by
  let : Nontrivial (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
    Submodule.Quotient.nontrivial_iff.mpr (pow_smul_top_ne_top (M := M) I hI hn)
  exact Module.length_pos

/-- The leading coefficient of the Samuel polynomial of a finite nonzero
module is positive. The existence and dimension theorems are not used. -/
lemma IsSamuelPoly.leadingCoeff_pos_of_nontrivial {I : Ideal R} {P : ℚ[X]}
    (hI : I.radical = maximalIdeal R) (hP : IsSamuelPoly R I M P) :
    0 < P.leadingCoeff := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < P.eval (n : ℚ) := by
    filter_upwards [hP, eventually_gt_atTop 0] with n hn hnpos
    rw [← hn.2]
    exact Nat.cast_pos.mpr (ENat.toNat_pos
      (samuelFunction_pos_of_nontrivial (M := M) I hI hnpos).ne' hn.1)
  by_cases hdeg : P.natDegree = 0
  · obtain ⟨n, hn⟩ := hpos.exists
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C] at hn
    simpa only [leadingCoeff, hdeg] using hn
  · by_contra! hlc
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)) hlc).comp
        (tendsto_natCast_atTop_atTop (R := ℚ))
    obtain ⟨n, hn, hn'⟩ := (hpos.and (ht.eventually_lt_atBot 0)).exists
    exact (lt_trans hn hn').false

end localModules

end SerrePositivity.HilbertSamuel
