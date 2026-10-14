module

public import SerrePositivity.CommutativeAlgebra.AdicPrincipalKernel
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusCriterion

/-! # 第0係数の生成からFontaine核の生成元を同定する

終域のpの非零因子性で核の飽和性を確認し、Witt環のp進完備性で
第0係数の生成元を核全体の生成元へ持ち上げる。
tiltの第0射影の核の計算は、独立の条件として明示する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.PerfectoidFrobeniusCriterion
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- Fontaine核の第0係数を一元で生成できれば、その元は核全体を生成する。 -/
theorem ker_fontaineTheta_eq_span_of_constantCoeff_generation
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (ξ : WittVector p (PreTilt S p)) (hξ : WittVector.fontaineTheta S p ξ = 0)
    (hgen : ∀ x : WittVector p (PreTilt S p), WittVector.fontaineTheta S p x = 0 →
      ∃ r : PreTilt S p, x.coeff 0 = ξ.coeff 0 * r) :
    RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {ξ} := by
  apply ker_eq_span_of_regular_of_mod_generator (p : WittVector p (PreTilt S p))
    (WittVector.fontaineTheta S p) (by simpa only [map_natCast] using hregular) ξ hξ
  intro x hx
  obtain ⟨r, hr⟩ := hgen x hx
  refine ⟨WittVector.teichmuller p r, ?_⟩
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
  change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _)
    (x - ξ * WittVector.teichmuller p r) = 0
  rw [map_sub, map_mul, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, hr, sub_self]

/-- tiltの第0射影の核が(q^p)なら、単元係数の特別な関係式がFontaine核を生成する。 -/
theorem ker_fontaineTheta_eq_span_of_tilt_coeff_kernel
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (q : PreTilt S p) (a : WittVector p (PreTilt S p)) (ha : IsUnit (a.coeff 0))
    (hξ : WittVector.fontaineTheta S p
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a) = 0)
    (htilt : RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) =
      Ideal.span {q ^ p}) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a} := by
  apply ker_fontaineTheta_eq_span_of_constantCoeff_generation S p hregular _ hξ
  intro x hx
  have hc : x.coeff 0 ∈ RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) := by
    change PreTilt.coeff 0 (x.coeff 0) = 0
    rw [← WittVector.mk_fontaineTheta, hx, map_zero]
  rw [htilt] at hc
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hc
  obtain ⟨u, hu⟩ := ha
  refine ⟨(↑(u⁻¹) : PreTilt S p) * r, ?_⟩
  have hco : ((p : WittVector p (PreTilt S p)) +
      WittVector.teichmuller p q ^ p * a).coeff 0 = q ^ p * a.coeff 0 := by
    change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* PreTilt S p)
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a) =
      q ^ p * a.coeff 0
    rw [map_add, map_mul, map_pow, WittVector.constantCoeff_apply,
      WittVector.coeff_p_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, WittVector.constantCoeff_apply, zero_add]
  rw [hco, hr, ← hu]
  simp [← mul_assoc]

/-- 正則なpを持つ環で、tilt射影の核の計算からFontaine核の単項性を供給する。
候補元の存在に単項核を仮定する循環を避ける。 -/
theorem fontaine_kernel_isPrincipal_of_tilt_coeff_kernel
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (π : S) (u : Sˣ) (hπ : (p : S) = u * π ^ p)
    (htilt : ∀ (q : PreTilt S p) (v : Sˣ), q.untilt = v * π →
      RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {q ^ p}) :
    (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal := by
  obtain ⟨q, v, a, hq, ha, hξ⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_primitive_kernel S p hF π u hπ
  rw [ker_fontaineTheta_eq_span_of_tilt_coeff_kernel S p hregular q a ha hξ (htilt q v hq)]
  infer_instance

/-- 逆に、単元係数のFontaine生成元からtiltの第0射影の核を計算する。
pの正則性はこの方向には必要ない。 -/
theorem tilt_coeff_kernel_eq_span_of_fontaine_generator
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (q : PreTilt S p) (a : WittVector p (PreTilt S p)) (ha : IsUnit (a.coeff 0))
    (hgen : RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a}) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {q ^ p} := by
  let θ := WittVector.fontaineTheta S p
  let ξ := (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a
  have hcoξ : ξ.coeff 0 = q ^ p * a.coeff 0 := by
    change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* PreTilt S p) ξ = _
    dsimp only [ξ]
    rw [map_add, map_mul, map_pow, WittVector.constantCoeff_apply,
      WittVector.coeff_p_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, WittVector.constantCoeff_apply, zero_add]
  apply le_antisymm
  · intro r hr
    have hr0 : PreTilt.coeff 0 r = 0 := hr
    have hu : r.untilt ∈ Ideal.span {(p : S)} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [PreTilt.mk_untilt_eq_coeff_zero, hr0]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hu
    obtain ⟨w, hw⟩ := surjective_fontaineTheta hF b
    have hm : WittVector.teichmuller p r - (p : WittVector p (PreTilt S p)) * w ∈
        RingHom.ker θ := by
      change θ (WittVector.teichmuller p r - (p : WittVector p (PreTilt S p)) * w) = 0
      rw [map_sub, map_mul, map_natCast, hw, WittVector.fontaineTheta_teichmuller, hb, sub_self]
    rw [hgen] at hm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hm
    have hh := congrArg (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _) hd
    have he : r = ξ.coeff 0 * d.coeff 0 := by
      simpa only [map_sub, map_mul, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, WittVector.coeff_p_zero, zero_mul,
        sub_zero] using hh
    rw [hcoξ, mul_assoc] at he
    exact Ideal.mem_span_singleton.mpr ⟨a.coeff 0 * d.coeff 0, he⟩
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    have hξ : ξ ∈ RingHom.ker θ := by
      rw [hgen]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hz : PreTilt.coeff 0 (q ^ p * a.coeff 0) = 0 := by
      rw [← hcoξ, ← WittVector.mk_fontaineTheta]
      change Ideal.Quotient.mk (Ideal.span {(p : S)}) (θ ξ) = 0
      rw [show θ ξ = 0 from hξ, map_zero]
    change PreTilt.coeff 0 (q ^ p) = 0
    apply (ha.map (PreTilt.coeff 0)).mul_right_eq_zero.mp
    simpa only [map_mul, mul_comm] using hz

/-- 正則なpを持つ環について、tilt射影の核の計算をperfectoidの四条件へ接続する。 -/
theorem isIntegralPerfectoid_of_regular_of_tilt_coeff_kernel
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (π : S) (u : Sˣ) (hπ : (p : S) = u * π ^ p)
    (htilt : ∀ (q : PreTilt S p) (v : Sˣ), q.untilt = v * π →
      RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) = Ideal.span {q ^ p}) :
    IsIntegralPerfectoid S p :=
  Or.inr ⟨Fact.out, inferInstance, ⟨π, u, hπ⟩, hF,
    fontaine_kernel_isPrincipal_of_tilt_coeff_kernel S p hregular hF π u hπ htilt⟩

end SerrePositivity.PerfectoidFrobeniusCriterion
