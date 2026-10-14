module

public import SerrePositivity.CommutativeAlgebra.PerfectoidRootTorsion

/-! # perfectoid環のpねじれ元のp乗根

Fontaine核の関係式から、pねじれ元をTeichmullerのuntiltで表示する。
tiltでp乗根を取ると、その根もpねじれとなる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open PerfectoidFrobeniusCriterion

/-- pねじれ元にはpねじれのp乗根が存在する。外部の構造定理を引用しない。 -/
theorem IsIntegralPerfectoid.exists_p_torsion_p_root
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (x : S) (hx : (p : S) * x = 0) : ∃ y : S, (p : S) * y = 0 ∧ y ^ p = x := by
  rcases hS with hsub | ⟨hp, hc, ⟨π, u, hpEq⟩, hF, hker⟩
  · exact ⟨0, mul_zero _, hsub.elim _ _⟩
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, a, hq, ha0, hgen⟩ :=
      exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hpEq
    let : IsReduced (PreTilt S p) := isReduced_of_perfectRing_charP (PreTilt S p) p
    obtain ⟨b, hb⟩ := surjective_fontaineTheta hF x
    have hdiv : (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a ∣
        (p : WittVector p (PreTilt S p)) * b := by
      apply Ideal.mem_span_singleton.mp
      rw [← hgen]
      change WittVector.fontaineTheta S p ((p : WittVector p (PreTilt S p)) * b) = 0
      simpa only [map_mul, map_natCast, hb] using hx
    obtain ⟨r, hqr, hr⟩ := witt_exists_teichmuller_representative_of_p_mul_dvd
      (PreTilt S p) p q a b p (Fact.out : p.Prime).pos ha0 hdiv
    have hrx : r.untilt = x := by
      have hm : b - WittVector.teichmuller p r ∈ RingHom.ker (WittVector.fontaineTheta S p) := by
        rw [hgen]
        exact Ideal.mem_span_singleton.mpr hr
      change WittVector.fontaineTheta S p (b - WittVector.teichmuller p r) = 0 at hm
      rw [map_sub, hb, WittVector.fontaineTheta_teichmuller] at hm
      exact (sub_eq_zero.mp hm).symm
    let t := (frobeniusEquiv (PreTilt S p) p).symm r
    have ht : t ^ p = r := frobeniusEquiv_symm_pow_p (PreTilt S p) p r
    have hqt : q * t = 0 := by
      apply IsReduced.eq_zero
      refine ⟨p, ?_⟩
      rw [mul_pow, ht]
      have hqp : q ^ p = q ^ (p - 1) * q := by
        simpa only [Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using pow_succ q (p - 1)
      rw [hqp, mul_assoc, hqr, mul_zero]
    have hπt : π * t.untilt = 0 := by
      have hh := congrArg (PreTilt.untilt : PreTilt S p →* S) hqt
      have hz : (0 : PreTilt S p).untilt = 0 := by
        rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
      rw [map_mul, hz, hq, mul_assoc] at hh
      exact v.isUnit.mul_right_eq_zero.mp hh
    refine ⟨t.untilt, ?_, ?_⟩
    · rw [hpEq]
      have hπp : π ^ p = π ^ (p - 1) * π := by
        simpa only [Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using pow_succ π (p - 1)
      rw [hπp, mul_assoc, mul_assoc, hπt, mul_zero, mul_zero]
    · rw [← map_pow, ht, hrx]

end SerrePositivity
