module

public import SerrePositivity.CommutativeAlgebra.WittDistinguishedTorsion
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusKernel
public import SerrePositivity.CommutativeAlgebra.PerfectoidCharacteristicP

/-! # 整perfectoid環のp冪ねじれ

Fontaine核のdistinguished生成元から、p冪で消える元はpで消えることを証明する。
特にpが冪零ならp=0となり、標数pの完全性・被約性を適用できる。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open PerfectoidFrobeniusCriterion
universe u

/-- 整perfectoid環のp冪ねじれはpで消える。四条件から証明し、外部引用を加えない。 -/
theorem IsIntegralPerfectoid.p_mul_eq_zero_of_pow_mul_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (n : ℕ) (x : S) (hx : (p : S) ^ n * x = 0) : (p : S) * x = 0 := by
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, one_mul, mul_zero] using congrArg (fun y ↦ (p : S) * y) hx
  rcases hS with hsub | ⟨hp, hc, ⟨π, u, hpEq⟩, hF, hker⟩
  · let : Subsingleton S := hsub
    exact Subsingleton.elim _ _
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, a, hq, hgen⟩ :=
      exists_untilt_unit_mul_and_kernel_generator S p hF hker π u hpEq
    let ξ : WittVector p (PreTilt S p) := (p : WittVector p (PreTilt S p)) +
      WittVector.teichmuller p q ^ p * a
    have hπ : π ^ p ∈ Ideal.span {(p : S)} := by
      have hh : (u : S) * π ^ p ∈ Ideal.span {(p : S)} := by
        rw [← hpEq]
        exact Ideal.subset_span (Set.mem_singleton _)
      simpa [mul_assoc] using (Ideal.span {(p : S)}).mul_mem_left (↑(u⁻¹) : S) hh
    have hqpow : q.untilt ^ p ∈ Ideal.span {(p : S)} := by
      rw [hq, mul_pow]
      exact (Ideal.span {(p : S)}).mul_mem_left _ hπ
    have hfirst : IsUnit (ξ.coeff 1) := by
      apply perfection_isUnit_of_coeff_zero (ModP S p) p
      change IsUnit (PreTilt.coeff 0 (ξ.coeff 1))
      rw [primitive_shape_firstCoeff_eq_one S p q a
        (coeff_zero_pow_eq_zero_of_untilt_pow_mem_p S p q hqpow)]
      exact isUnit_one
    let : IsReduced (PreTilt S p) := isReduced_of_perfectRing_charP (PreTilt S p) p
    obtain ⟨w, hw⟩ := surjective_fontaineTheta hF x
    have hdiv : ξ ∣ (p : WittVector p (PreTilt S p)) ^ n * w := by
      apply Ideal.mem_span_singleton.mp
      rw [← hgen]
      change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) ^ n * w) = 0
      simpa only [map_mul, map_pow, map_natCast, hw] using hx
    have hd := witt_distinguished_dvd_p_mul_of_dvd_p_pow_mul (PreTilt S p) p ξ w
      hfirst n (Nat.pos_of_ne_zero hn) hdiv
    have hm : (p : WittVector p (PreTilt S p)) * w ∈
        RingHom.ker (WittVector.fontaineTheta S p) := by
      rw [hgen]
      exact Ideal.mem_span_singleton.mpr hd
    change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) * w) = 0 at hm
    simpa only [map_mul, map_natCast, hw] using hm

/-- pが冪零の整perfectoid環ではp=0。 -/
theorem IsIntegralPerfectoid.p_eq_zero_of_isNilpotent
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (hp : IsNilpotent (p : S)) : (p : S) = 0 := by
  obtain ⟨n, hn⟩ := hp
  simpa only [mul_one] using hS.p_mul_eq_zero_of_pow_mul_eq_zero S p n 1
    (by simpa only [mul_one] using hn)

end SerrePositivity
