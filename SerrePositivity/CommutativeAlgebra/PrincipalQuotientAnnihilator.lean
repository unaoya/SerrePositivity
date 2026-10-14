module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

/-! # 正則元の冪による商における零化元

r^Nによる商でrを零化する元はr^(N-1)の倍数である。
指数の不等式から、その元の指定した冪が零になることを導く。
-/

@[expose] public section
namespace SerrePositivity
variable (R : Type*) [CommRing R]

/-- 正則元の冪による商で、その元の零化元は指定した冪で消える。 -/
theorem pow_eq_zero_of_mul_eq_zero_mod_regular_pow (r : R)
    (hreg : Function.Injective (fun z : R ↦ r * z)) (N k : ℕ) (hN : 0 < N)
    (hbound : N ≤ (N - 1) * k) (z : R ⧸ Ideal.span {r ^ N})
    (hz : Ideal.Quotient.mk (Ideal.span {r ^ N}) r * z = 0) : z ^ k = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have ha : r * a ∈ Ideal.span {r ^ N} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hab : a = r ^ (N - 1) * b := by
    apply hreg
    change r * a = r * (r ^ (N - 1) * b)
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hN]
    exact hb
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  rw [hab, mul_pow, ← pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow r hbound) _

end SerrePositivity
