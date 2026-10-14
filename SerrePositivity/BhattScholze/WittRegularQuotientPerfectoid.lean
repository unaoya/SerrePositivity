module

public import SerrePositivity.BhattScholze.WittQuotientTiltKernelRegular
public import SerrePositivity.CommutativeAlgebra.PerfectoidFontainePrincipal
public import SerrePositivity.CommutativeAlgebra.AdicRegularQuotient

/-! # 第0係数が正則なdistinguished Witt商のperfectoid性

既存のIsIntegralPerfectoidとFontaine核判定を使う具体的な定理。
商の古典的p完備性は明示的な仮定。一般のpねじれ商やWitt復元はまだ含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- d₀が正則ならW(k)/(d)ではpが正則。既存の正則商APIにWitt剰余同型を供給する。 -/
theorem wittQuotient_p_mul_injective_of_coeff_zero_regular (d : WittVector p k)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Injective (fun x : WittVector p k ⧸ Ideal.span {d} ↦
      (p : WittVector p k ⧸ Ideal.span {d}) * x) := by
  have hp : IsSMulRegular (WittVector p k) (p : WittVector p k) :=
    (wittDeltaStructure_isPerfect p k).p_mul_injective
  have hd : IsSMulRegular (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) d) := by
    intro x y hxy
    let e := WittVector.quotientPEquiv (p := p) (k := k)
    apply e.injective
    apply hreg
    have h := congrArg e hxy
    change e (Ideal.Quotient.mk _ d * x) = e (Ideal.Quotient.mk _ d * y) at h
    rw [map_mul, map_mul] at h
    exact h
  exact isSMulRegular_quotient_span_of_regular_mod (WittVector p k) (p : WittVector p k) d hp hd

variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 完備なdistinguished Witt商でd₀が正則なら、Fontaine核は単項。
既存引用への依存なしに、tilt核と単元係数の原始元から証明する。 -/
theorem wittRegularQuotient_fontaine_kernel_isPrincipal
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)).IsPrincipal := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let q := Ideal.Quotient.mk (Ideal.span {d})
  obtain ⟨u, hu⟩ := exists_teichmuller_add_p_mul_unit_of_distinguished p k d hd
  obtain ⟨a, ha⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (d.coeff 0)
  change a ^ p = d.coeff 0 at ha
  let r := wittQuotientTiltMap p k d a
  let w := Units.map q.toMonoidHom u
  let v := -w⁻¹
  have hpEq : (p : S) = (v : S) * r.untilt ^ p := by
    have hq : q (WittVector.teichmuller p a) ^ p + (p : S) * (w : S) = 0 := by
      have h := congrArg q hu
      rw [map_add, map_mul, map_natCast] at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))] at h
      change 0 = q (WittVector.teichmuller p (d.coeff 0)) + (p : S) * q (u : WittVector p k) at h
      change q (WittVector.teichmuller p a) ^ p + (p : S) * q (u : WittVector p k) = 0
      rw [← map_pow, ← map_pow, ha]
      exact h.symm
    have hπ := eq_neg_of_add_eq_zero_left hq
    rw [wittQuotientTiltMap_untilt, hπ]
    simp [v, mul_comm, mul_assoc]
  have hF : Function.Surjective (frobenius (ModP S p) p) :=
    (wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d})
  obtain ⟨b, hb⟩ := surjective_fontaineTheta hF (-(v : S))
  have hb0 : IsUnit (b.coeff 0) := by
    apply perfection_isUnit_of_coeff_zero (ModP S p) p
    change IsUnit (PreTilt.coeff 0 (b.coeff 0))
    rw [← WittVector.mk_fontaineTheta, hb]
    exact (v.isUnit.neg).map (Ideal.Quotient.mk (Ideal.span {(p : S)}))
  have hξ : WittVector.fontaineTheta S p
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p r ^ p * b) = 0 := by
    rw [map_add, map_mul, map_pow, map_natCast, WittVector.fontaineTheta_teichmuller, hb, hpEq]
    ring
  have htilt : RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {r ^ p} := by
    rw [wittQuotientTilt_coeff_zero_kernel_eq_span p k d hreg]
    congr 1
    change {wittQuotientTiltMap p k d (d.coeff 0)} = {wittQuotientTiltMap p k d a ^ p}
    rw [← map_pow, ha]
  rw [PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_tilt_coeff_kernel S p
    (wittQuotient_p_mul_injective_of_coeff_zero_regular p k d hreg) r b hb0 hξ htilt]
  infer_instance

/-- 第0係数が正則なdistinguished Witt元の古典的p進完備商は整perfectoid。
定義の四条件を既存APIにより供給し、一般商の完備性を追加結論しない。 -/
theorem wittRegularQuotient_isIntegralPerfectoid
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    IsIntegralPerfectoid (WittVector p k ⧸ Ideal.span {d}) p :=
  Or.inr ⟨Fact.out, inferInstance,
    witt_distinguished_quotient_exists_unit_mul_pow_p p k d hd,
    (wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}),
    wittRegularQuotient_fontaine_kernel_isPrincipal p k d hd hreg⟩

end SerrePositivity.BhattScholze
