module

public import SerrePositivity.CommutativeAlgebra.PerfectoidCharacteristicP
public import SerrePositivity.CommutativeAlgebra.FrobeniusRootKernels
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # pが零である完全環のperfectoid性

N3の標数p商の候補に、既存のIsIntegralPerfectoidの四条件を供給する。
一般strict p環のWitt復元や一般主イデアル商のperfection核は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- p=0の完全環は、既存の四条件による整perfectoid環である。零環も含む。 -/
theorem isIntegralPerfectoid_of_perfectRing_p_eq_zero [PerfectRing R p]
    (hp : (p : R) = 0) : IsIntegralPerfectoid R p := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact Or.inl hs
  · let := hn
    have hI : Ideal.span {(p : R)} = ⊥ := by simp [hp]
    let : IsAdicComplete (Ideal.span {(p : R)}) R := by rw [hI]; infer_instance
    have hnonunit : ¬ IsUnit (p : R) := by rw [hp]; exact not_isUnit_zero
    let : Fact (¬ IsUnit (p : R)) := ⟨hnonunit⟩
    let E : ModP R p ≃+* R := (Ideal.quotEquivOfEq hI).trans (RingEquiv.quotientBot R)
    let : PerfectRing (ModP R p) p := by
      refine ⟨⟨?_, ?_⟩⟩
      · intro x y hxy
        apply E.injective
        apply (PerfectRing.bijective_frobenius (R := R) (p := p)).1
        simpa only [frobenius_def, ← map_pow] using congrArg E hxy
      · intro x
        obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2 (E x)
        refine ⟨E.symm y, ?_⟩
        apply E.injective
        simpa only [frobenius_def, ← map_pow, E.apply_symm_apply] using hy
    let : IsReduced (ModP R p) := isReduced_of_perfectRing_charP (ModP R p) p
    have hker : RingHom.ker (WittVector.fontaineTheta R p) =
        Ideal.span {(p : WittVector p (PreTilt R p))} := by
      apply le_antisymm
      · intro w hw
        apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero w).mpr
        apply Perfection.ext
        intro n
        change PreTilt.coeff n (w.coeff 0) = 0
        apply eq_zero_of_pow_eq_zero (n := p ^ n)
        have h0 : PreTilt.coeff 0 (w.coeff 0) = 0 := by
          rw [← WittVector.mk_fontaineTheta, show WittVector.fontaineTheta R p w = 0 from hw]
          exact map_zero _
        simpa only [zero_add, h0] using
          compatibleRoots_pow p (fun m ↦ PreTilt.coeff m (w.coeff 0))
            (fun m ↦ PreTilt.coeff_pow_p _ m) 0 n
      · apply Ideal.span_le.mpr
        rw [Set.singleton_subset_iff]
        change WittVector.fontaineTheta R p (p : WittVector p (PreTilt R p)) = 0
        simpa only [map_natCast] using hp
    refine Or.inr ⟨hnonunit, inferInstance, ⟨0, 1, ?_⟩, ?_, ?_⟩
    · simp [hp, (Fact.out : p.Prime).ne_zero]
    · exact (PerfectRing.bijective_frobenius (R := ModP R p) (p := p)).2
    · rw [hker]
      infer_instance

end SerrePositivity.BhattScholze
