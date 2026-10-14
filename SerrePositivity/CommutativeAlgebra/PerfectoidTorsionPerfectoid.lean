module

public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionTilt
public import SerrePositivity.CommutativeAlgebra.PerfectoidFontainePrincipal
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality

/-! # pねじれを除いた商のperfectoid性

元のFontaine生成元からtilt射影の核を計算し、ねじれ商へ移す。
untiltの自然性とpの正則性で、商のFontaine核の生成元を同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open PerfectoidFrobeniusCriterion

/-- 整perfectoid環のpねじれ商は整perfectoid。四条件から証明する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_isIntegralPerfectoid
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p := by
  rcases hS with hsub | hdata
  · let : Subsingleton S := hsub
    exact Or.inl inferInstance
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨hp, hc, ⟨π, u, hπ⟩, hF, hker⟩ := hdata
  let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
  let := hc
  let Q := S ⧸ pTorsionIdeal S p
  let f := Ideal.Quotient.mk (pTorsionIdeal S p)
  let hcQ : IsAdicComplete (Ideal.span {(p : Q)}) Q := hS.pTorsionQuotient_isAdicComplete S p
  by_cases hsub : Subsingleton Q
  · exact Or.inl hsub
  have hpQ : ¬ IsUnit (p : Q) := by
    intro hu
    have ht : Ideal.span {(p : Q)} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
    have hh : IsHausdorff (⊤ : Ideal Q) Q := ht ▸ hcQ.toIsHausdorff
    exact hsub hh.subsingleton
  let : Fact (¬ IsUnit (p : Q)) := ⟨hpQ⟩
  obtain ⟨q, v, a, hq, ha0, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hπ
  have htiltS := tilt_coeff_kernel_eq_span_of_fontaine_generator S p hF q a ha0 hgen
  let g : PreTilt S p →+* PreTilt Q p := Perfection.map p (pTorsionQuotientModPMap S p)
  let qQ : PreTilt Q p := g q
  have htiltQ : RingHom.ker (PreTilt.coeff 0 : PreTilt Q p →+* ModP Q p) =
      Ideal.span {qQ ^ p} := by
    have hh := hS.pTorsionQuotient_preTilt_coeff_kernel S p
    change (RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p)).map g =
      RingHom.ker (PreTilt.coeff 0 : PreTilt Q p →+* ModP Q p) at hh
    rw [htiltS, Ideal.map_span, Set.image_singleton, map_pow] at hh
    exact hh.symm
  let uQ : Qˣ := Units.map f.toMonoidHom u
  let vQ : Qˣ := Units.map f.toMonoidHom v
  have hπQ : (p : Q) = uQ * (f π) ^ p := by
    change (p : Q) = f (u : S) * (f π) ^ p
    simpa only [map_mul, map_pow, map_natCast] using congrArg f hπ
  have hqQ : qQ.untilt = vQ * f π := by
    change PreTilt.untilt (Perfection.map p (modPMap p f) q) = f (v : S) * f π
    rw [untilt_map, hq, map_mul]
  let w : Qˣ := uQ * (vQ⁻¹) ^ p
  have hpq : (p : Q) = (w : Q) * qQ.untilt ^ p := by
    rw [hqQ, mul_pow, hπQ]
    change (uQ : Q) * (f π) ^ p =
      ((uQ : Q) * (↑(vQ⁻¹) : Q) ^ p) * ((vQ : Q) ^ p * (f π) ^ p)
    calc
      _ = (uQ : Q) * (((↑(vQ⁻¹) : Q) * (vQ : Q)) ^ p * (f π) ^ p) := by simp
      _ = _ := by simp only [mul_pow]; ring
  have hFQ := hS.surjective_pow_mod_p_quotient S p (pTorsionIdeal S p)
  obtain ⟨b, hb⟩ := surjective_fontaineTheta hFQ (-(w : Q))
  have hb0 : IsUnit (b.coeff 0) := by
    apply perfection_isUnit_of_coeff_zero (ModP Q p) p
    change IsUnit (PreTilt.coeff 0 (b.coeff 0))
    rw [← WittVector.mk_fontaineTheta, hb]
    exact (w.isUnit.neg).map (Ideal.Quotient.mk (Ideal.span {(p : Q)}))
  have hξ : WittVector.fontaineTheta Q p
      ((p : WittVector p (PreTilt Q p)) + WittVector.teichmuller p qQ ^ p * b) = 0 := by
    rw [map_add, map_mul, map_pow, map_natCast, WittVector.fontaineTheta_teichmuller, hb, hpq]
    ring
  have hkerQ : (RingHom.ker (WittVector.fontaineTheta Q p)).IsPrincipal := by
    rw [ker_fontaineTheta_eq_span_of_tilt_coeff_kernel Q p
      (hS.pTorsionQuotient_p_mul_injective S p) qQ b hb0 hξ htiltQ]
    infer_instance
  exact Or.inr ⟨hpQ, hcQ, ⟨f π, uQ, hπQ⟩, hFQ, hkerQ⟩

end SerrePositivity
