module

public import SerrePositivity.BhattScholze.WittDistinguished
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusCriterion

/-! # perfectoid環のFontaine核のdistinguished生成元

既存のFontaine核判定を再利用する。pねじれを持つperfectoid環も含む。
-/

@[expose] public noncomputable section
universe u
open SerrePositivity.PerfectoidFrobeniusCriterion
namespace SerrePositivity.BhattScholze
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- perfectoidの四条件から、標準Witt δ構造でdistinguishedなFontaine核生成元を得る。 -/
theorem exists_distinguished_fontaine_kernel_generator
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ d : WittVector p (PreTilt S p),
      (wittDeltaStructure p (PreTilt S p)).IsDistinguished d ∧
      RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {d} := by
  obtain ⟨q, v, a, hq, _, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hpEq
  let d : WittVector p (PreTilt S p) := (p : WittVector p (PreTilt S p)) +
    WittVector.teichmuller p q ^ p * a
  refine ⟨d, ?_, hgen⟩
  apply (wittDeltaStructure_isDistinguished_iff p (PreTilt S p) d).mpr
  apply perfection_isUnit_of_coeff_zero (ModP S p) p
  change IsUnit (PreTilt.coeff 0 (d.coeff 1))
  have hπ : π ^ p ∈ Ideal.span {(p : S)} := by
    have hh : (u : S) * π ^ p ∈ Ideal.span {(p : S)} := by
      rw [← hpEq]
      exact Ideal.mem_span_singleton_self _
    simpa [mul_assoc] using (Ideal.span {(p : S)}).mul_mem_left (↑(u⁻¹) : S) hh
  have hqpow : q.untilt ^ p ∈ Ideal.span {(p : S)} := by
    rw [hq, mul_pow]
    exact (Ideal.span {(p : S)}).mul_mem_left _ hπ
  rw [primitive_shape_firstCoeff_eq_one S p q a
    (coeff_zero_pow_eq_zero_of_untilt_pow_mem_p S p q hqpow)]
  exact isUnit_one

end SerrePositivity.BhattScholze
