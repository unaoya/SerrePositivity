module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaDividedPowerCoefficients
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # 分冪展開係数の恒等式

任意Q代数に移せる有理数の等式を先に示す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime]

/-- 付値計算したFrobenius係数は、二項展開の実際の係数と一致する。 -/
theorem dividedPowerFrobeniusCoefficient_div_factorial (n i : ℕ) (hi : i ≤ n) :
    dividedPowerFrobeniusCoefficient p n i / ((p * i).factorial : ℚ) =
      (n.choose i : ℚ) * (p : ℚ) ^ (n - i) / ((p : ℚ) * (n.factorial : ℚ)) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hc : (n.choose i : ℚ) * (i.factorial : ℚ) * ((n - i).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  rw [dividedPowerFrobeniusCoefficient]
  field_simp
  rw [← hc]
  ring

/-- 付値計算した冪の係数は、γ_(pn)(x)へ掛ける実際の係数と一致する。 -/
theorem dividedPowerPowerCoefficient_div_factorial (n : ℕ) :
    dividedPowerPowerCoefficient p n / ((p * n).factorial : ℚ) =
      1 / ((p : ℚ) * (n.factorial : ℚ) ^ p) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [dividedPowerPowerCoefficient]
  field_simp

/-- 有理係数の環射の下での、Frobenius型二項式の実際の分冪展開。 -/
theorem dividedPower_frobenius_expansion {R : Type u} [CommRing R]
    (f : ℚ →+* R) (x z : R) (n : ℕ) :
    f (1 / ((p : ℚ) * (n.factorial : ℚ))) * (x ^ p + f (p : ℚ) * z) ^ n =
      ∑ i ∈ Finset.range (n + 1), f (dividedPowerFrobeniusCoefficient p n i) *
        (f (1 / ((p * i).factorial : ℚ)) * x ^ (p * i)) * z ^ (n - i) := by
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hni : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcQ : 1 / ((p : ℚ) * (n.factorial : ℚ)) * (p : ℚ) ^ (n - i) * (n.choose i : ℚ) =
      dividedPowerFrobeniusCoefficient p n i * (1 / ((p * i).factorial : ℚ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using
      (dividedPowerFrobeniusCoefficient_div_factorial (p := p) n i hni).symm
  have hc := congrArg f hcQ
  simp only [map_mul, map_pow, map_natCast] at hc
  rw [mul_pow, ← pow_mul]
  simp only [map_natCast]
  calc
    _ = (f (1 / ((p : ℚ) * (n.factorial : ℚ))) * (p : R) ^ (n - i) *
        (n.choose i : R)) * x ^ (p * i) * z ^ (n - i) := by ring
    _ = _ := by rw [hc]; ring

/-- 有理係数の環射の下での、γ_n(x)^p/pの実際の分冪展開。 -/
theorem dividedPower_power_expansion {R : Type u} [CommRing R]
    (f : ℚ →+* R) (x : R) (n : ℕ) :
    f (1 / (p : ℚ)) * (f (1 / (n.factorial : ℚ)) * x ^ n) ^ p =
      f (dividedPowerPowerCoefficient p n) *
        (f (1 / ((p * n).factorial : ℚ)) * x ^ (p * n)) := by
  have hcQ : 1 / (p : ℚ) * (1 / (n.factorial : ℚ)) ^ p =
      dividedPowerPowerCoefficient p n * (1 / ((p * n).factorial : ℚ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_inv_rev, inv_pow,
      mul_comm, mul_left_comm, mul_assoc]
      using (dividedPowerPowerCoefficient_div_factorial (p := p) n).symm
  have hc := congrArg f hcQ
  simp only [map_mul, map_pow] at hc
  rw [mul_pow, ← pow_mul, Nat.mul_comm n p]
  calc
    _ = (f (1 / (p : ℚ)) * f (1 / (n.factorial : ℚ)) ^ p) * x ^ (p * n) := by ring
    _ = _ := by rw [hc]; ring

end SerrePositivity.BhattScholze
