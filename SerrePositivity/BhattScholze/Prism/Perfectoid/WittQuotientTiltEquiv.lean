module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTiltSurjective
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientFontaineIso
public import SerrePositivity.CommutativeAlgebra.AdicBoundedTorsionQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidCharacteristicP
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # 完全prismのWitt表示における一般商のtilt同型

W(k)のd完備性からkのd₀完備性をF5で供給し、F6による全射性と既存の単射性を合成する。
商のp正則性・d₀正則性・Fontaine核進分離性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- Witt環がd進完備なら、係数環はd₀進完備。mod pの被約性から有界ねじれを供給する。 -/
theorem witt_coeff_zero_isAdicComplete (d : WittVector p k)
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)] :
    IsAdicComplete (Ideal.span {d.coeff 0}) k := by
  let M := WittVector p k ⧸ Ideal.span {(p : WittVector p k)}
  let e : M ≃+* k := WittVector.quotientPEquiv
  let q := Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)})
  let : IsReduced k := isReduced_of_perfectRing_charP k p
  let : IsReduced M := isReduced_of_injective e.toRingHom e.injective
  have hb : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, q d ^ n * x = 0 → q d ^ N * x = 0 := by
    refine ⟨1, ?_⟩
    intro n x hx
    rw [pow_one]
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, one_mul] at hx
      rw [hx, mul_zero]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      apply eq_zero_of_pow_eq_zero (n := m + 1)
      rw [mul_pow, pow_succ' x m, ← mul_assoc, hx, zero_mul]
  have hM := isAdicComplete_principal_quotient_of_bounded_torsion (WittVector p k) d
    (p : WittVector p k) hb
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {q d}) e).mpr hM
  have he : e (q d) = d.coeff 0 := rfl
  simpa only [Ideal.map_span, Set.image_singleton, he] using h

variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 完備なdistinguished Witt商の標準tilt射は全単射。d₀正則性を追加しない。 -/
theorem wittQuotientTiltMap_bijective (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Bijective (wittQuotientTiltMap p k d) := by
  let := witt_coeff_zero_isAdicComplete p k d
  exact ⟨wittQuotientTiltMap_injective p k d hd, wittQuotientTiltMap_surjective p k d⟩

/-- 標準tilt射を環同型として束ねる。 -/
def wittQuotientTiltEquiv (hd : (wittDeltaStructure p k).IsDistinguished d) :
    k ≃+* PreTilt (WittVector p k ⧸ Ideal.span {d}) p :=
  RingEquiv.ofBijective (wittQuotientTiltMap p k d) (wittQuotientTiltMap_bijective p k d hd)

end SerrePositivity.BhattScholze
