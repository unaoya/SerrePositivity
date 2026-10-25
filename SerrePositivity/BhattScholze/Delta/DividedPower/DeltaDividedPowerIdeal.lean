module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaFactorialDivision

/-! # δ環のp除算可能イデアルと階乗分母の閉性

I={x | p∣x^p}を既存Frobenius liftの逆像イデアルとして具体化する。
正の次数の階乗分母をI内に選べることを示す。分冪公理は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- pで割れるp乗を持つ元のイデアル。 -/
def primeDividedPowerIdeal (D : DeltaStructure p A) : Ideal A :=
  Ideal.comap D.frobeniusLift (Ideal.span {(p : A)})

/-- Frobenius liftの逆像という定義はp∣x^pと同値。 -/
theorem mem_primeDividedPowerIdeal (D : DeltaStructure p A) (x : A) :
    x ∈ D.primeDividedPowerIdeal ↔ (p : A) ∣ x ^ p := by
  change D.frobeniusLift x ∈ Ideal.span {(p : A)} ↔ _
  rw [Ideal.mem_span_singleton, D.frobeniusLift_apply]
  exact dvd_add_left (dvd_mul_right (p : A) (D.delta x))

/-- 正の次数のp進階乗分母は、p除算可能イデアルの中に選べる。 -/
theorem exists_factorial_valuation_quotient_mem (D : DeltaStructure p A) (n : ℕ) :
    ∀ x : A, x ∈ D.primeDividedPowerIdeal → ∃ w : A,
      (p : A) ^ padicValNat p n.factorial * w = x ^ n ∧
      (n ≠ 0 → w ∈ D.primeDividedPowerIdeal) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · subst n
        exact ⟨1, by simp, by simp⟩
      obtain ⟨z, hz⟩ := (D.mem_primeDividedPowerIdeal x).mp hx
      have hzmem := (D.mem_primeDividedPowerIdeal z).mpr (D.prime_dvd_divided_pow hz)
      have hk : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn)
        (Fact.out : p.Prime).one_lt
      have he : padicValNat p n.factorial = padicValNat p (n / p).factorial + n / p := by
        rw [← padicValNat_mul_div_factorial (p := p) n, padicValNat_factorial_mul]
      by_cases hk0 : n / p = 0
      · refine ⟨x ^ n, ?_, fun _ ↦ ?_⟩
        · simp [he, hk0]
        · exact (D.primeDividedPowerIdeal).pow_mem_of_mem hx n (Nat.pos_of_ne_zero hn)
      · obtain ⟨w, hw, hwmem⟩ := ih (n / p) hk z hzmem
        refine ⟨w * x ^ (n % p), ?_, fun _ ↦ ?_⟩
        · calc
            (p : A) ^ padicValNat p n.factorial * (w * x ^ (n % p)) =
                ((p : A) * z) ^ (n / p) * x ^ (n % p) := by
              rw [mul_pow, ← hw, he, pow_add]
              ring
            _ = x ^ n := by rw [← hz, ← pow_mul, ← pow_add, Nat.div_add_mod]
        · exact (D.primeDividedPowerIdeal).mul_mem_right _ (hwmem hk0)

/-- p局所性の下で、正の次数の階乗分母も同じイデアルに選べる。 -/
theorem exists_factorial_quotient_mem (D : DeltaStructure p A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) {x : A}
    (hx : x ∈ D.primeDividedPowerIdeal) (n : ℕ) : ∃ w : A,
    (n.factorial : A) * w = x ^ n ∧ (n ≠ 0 → w ∈ D.primeDividedPowerIdeal) := by
  obtain ⟨k, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hm (hm0 ▸ dvd_zero p)
  have hk : padicValNat p n.factorial = k := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨w, hw, hwmem⟩ := D.exists_factorial_valuation_quotient_mem n x hx
  obtain ⟨v, hv⟩ := hlocal m hm
  refine ⟨(v⁻¹ : Aˣ) * w, ?_, fun hn ↦ ?_⟩
  · rw [← hw, hk, hfac, Nat.cast_mul, Nat.cast_pow, ← hv]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  · exact (D.primeDividedPowerIdeal).mul_mem_left _ (hwmem hn)

end SerrePositivity.BhattScholze.DeltaStructure
