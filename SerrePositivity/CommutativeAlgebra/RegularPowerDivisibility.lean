module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 被約な主元商からの冪の整除性

正則元rによる商が被約なら、r^(k*n)がx^kを割ることからr^nがxを割る。
一段ずつrで割り、正則性によってr^kをキャンセルする。
-/

@[expose] public section
namespace SerrePositivity
variable (R : Type*) [CommRing R]

/-- 被約な正則主元商では、冪の整除性から元の整除性が従う。 -/
theorem regular_pow_dvd_of_pow_dvd (r : R)
    (hreg : IsLeftRegular r) [IsReduced (R ⧸ Ideal.span {r})]
    (k : ℕ) (hk : 0 < k) (n : ℕ) (x : R) (hx : r ^ (k * n) ∣ x ^ k) :
    r ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hdiv : r ∣ x ^ k :=
      dvd_trans (dvd_pow_self r (by positivity : k * (n + 1) ≠ 0)) hx
    have hz : (Ideal.Quotient.mk (Ideal.span {r}) x) ^ k = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    have hxr : r ∣ x := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨k, hz⟩))
    obtain ⟨y, rfl⟩ := hxr
    have hy : r ^ (k * n) ∣ y ^ k := by
      obtain ⟨b, hb⟩ := hx
      refine ⟨b, ?_⟩
      apply hreg.pow k
      change r ^ k * y ^ k = r ^ k * (r ^ (k * n) * b)
      rw [← mul_pow, hb, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    obtain ⟨b, hb⟩ := ih y hy
    refine ⟨b, ?_⟩
    rw [hb, pow_succ']
    ring

end SerrePositivity
