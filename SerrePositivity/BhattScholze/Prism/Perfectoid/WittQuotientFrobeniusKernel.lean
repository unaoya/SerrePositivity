module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientModP

/-! # Witt商mod pのFrobenius核の生成元

係数環の完全性でd₀のp乗根aを選び、W(k)/(d)/pのp乗零化元が[a]の像で
生成されることを証明する。Fontaine核の同定やperfectoid性は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- d₀のp^n乗根aのTeichmüller像は、Witt商mod pの反復Frobenius核を生成する。
dがdistinguishedであるという仮定はこの有限商の計算には不要。 -/
theorem wittQuotientModP_pow_prime_pow_eq_zero_iff_mem_span
    (d : WittVector p k) (n : ℕ) (a : k)
    (ha : a ^ (p ^ n) = d.coeff 0)
    (z : (WittVector p k ⧸ Ideal.span {d}) ⧸
      Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})}) :
    z ^ (p ^ n) = 0 ↔ z ∈ Ideal.span {
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a))} := by
  let e := wittQuotientModPEquiv p k d
  let q := Ideal.Quotient.mk (Ideal.span {d.coeff 0})
  let g := Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
    (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a))
  have heg : e g = q a := by simp [e, g, q]
  have hqa : (q a) ^ (p ^ n) = 0 := by
    rw [← map_pow, ha]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e z)
    have hbp : b ^ (p ^ n) ∈ Ideal.span {d.coeff 0} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (b ^ (p ^ n)) = 0
      rw [map_pow]
      change q b = e z at hb
      rw [hb, ← map_pow, hz, map_zero]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hbp
    obtain ⟨v, hv⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p ^ n)).2 c
    change v ^ (p ^ n) = c at hv
    have hbv : b = a * v := by
      apply (PerfectRing.bijective_frobenius (R := k) (p := p ^ n)).1
      change b ^ (p ^ n) = (a * v) ^ (p ^ n)
      rw [mul_pow, ha, hv]
      exact hc
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.symm (q v), ?_⟩
    apply e.injective
    rw [map_mul, heg, RingEquiv.apply_symm_apply, ← map_mul, ← hbv]
    exact hb.symm
  · intro hz
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hz
    change z = g * y at hy
    have hgp : g ^ (p ^ n) = 0 := by
      apply e.injective
      rw [map_pow, heg, hqa, map_zero]
    rw [hy, mul_pow, hgp, zero_mul]

/-- 最初のFrobenius核の具体的な生成元。 -/
theorem wittQuotientModP_pow_eq_zero_iff_mem_span (d : WittVector p k) (a : k)
    (ha : a ^ p = d.coeff 0)
    (z : (WittVector p k ⧸ Ideal.span {d}) ⧸
      Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})}) :
    z ^ p = 0 ↔ z ∈ Ideal.span {
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a))} := by
  simpa only [pow_one] using wittQuotientModP_pow_prime_pow_eq_zero_iff_mem_span
    p k d 1 a (by simpa only [pow_one] using ha) z

end SerrePositivity.BhattScholze
