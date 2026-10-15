module

public import SerrePositivity.BhattScholze.DeltaDividedPowerStep
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorization.Basic

/-! # Lemma 2.35の階乗分母の可除性

δ環のp除算閉性から、すべての階乗分母の存在を示す。
p局所性は非p倍の自然数が単元であるという仮定で明示する。
分冪構造の公理や分冪包との同定はここでは主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- x^pがpで割り切れるδ環では、p^val_p(n!)はx^nを割り切る。 -/
theorem factorial_valuation_pow_dvd (D : DeltaStructure p A) (n : ℕ) :
    ∀ x : A, (p : A) ∣ x ^ p → (p : A) ^ padicValNat p n.factorial ∣ x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · simp [hn]
      obtain ⟨z, hz⟩ := hx
      have hz' := D.prime_dvd_divided_pow hz
      have hk : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn)
        (Fact.out : p.Prime).one_lt
      obtain ⟨w, hw⟩ := ih (n / p) hk z hz'
      have he : padicValNat p n.factorial = padicValNat p (n / p).factorial + n / p := by
        rw [← padicValNat_mul_div_factorial (p := p) n, padicValNat_factorial_mul]
      refine ⟨w * x ^ (n % p), ?_⟩
      calc
        x ^ n = (x ^ p) ^ (n / p) * x ^ (n % p) := by
          rw [← pow_mul, ← pow_add, Nat.div_add_mod]
        _ = ((p : A) * z) ^ (n / p) * x ^ (n % p) := by rw [hz]
        _ = (p : A) ^ padicValNat p n.factorial * (w * x ^ (n % p)) := by
          rw [mul_pow, hw, he, pow_add]
          ring

/-- 非p倍の自然数が単元であるδ環で、x^pのp除算から全階乗分母を得る。 -/
theorem factorial_dvd_pow_of_prime_dvd_pow (D : DeltaStructure p A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) {x : A}
    (hx : (p : A) ∣ x ^ p) (n : ℕ) : (n.factorial : A) ∣ x ^ n := by
  obtain ⟨k, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hm (hm0 ▸ dvd_zero p)
  have hk : padicValNat p n.factorial = k := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨w, hw⟩ := D.factorial_valuation_pow_dvd n x hx
  obtain ⟨v, hv⟩ := hlocal m hm
  refine ⟨(v⁻¹ : Aˣ) * w, ?_⟩
  rw [hw, hk, hfac, Nat.cast_mul, Nat.cast_pow, ← hv]
  simp only [mul_assoc, Units.mul_inv_cancel_left]

end SerrePositivity.BhattScholze.DeltaStructure
