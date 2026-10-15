module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # Lemma 2.36の分冪展開係数のp可積分性

著者公開版p.23の係数をpで割った値について、既存p進付値で評価する。
分冪生成部分環のδ安定性への数論的入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime]

/-- φ(y^n/n!)/pのi番目の分冪展開係数。 -/
def dividedPowerFrobeniusCoefficient (p n i : ℕ) : ℚ :=
  ((p * i).factorial : ℚ) / (i.factorial : ℚ) *
    ((p : ℚ) ^ (n - i) / ((n - i).factorial : ℚ)) / (p : ℚ)

/-- (y^n/n!)^p/pをγ_(pn)(y)で書く際の係数。 -/
def dividedPowerPowerCoefficient (p n : ℕ) : ℚ :=
  ((p * n).factorial : ℚ) / ((n.factorial : ℚ) ^ p * (p : ℚ))

/-- Frobenius展開係数のp進付値の正確な式。 -/
theorem dividedPowerFrobeniusCoefficient_valuation (n i : ℕ) (hi : i ≤ n) :
    padicValRat p (dividedPowerFrobeniusCoefficient p n i) =
      (n : ℤ) - padicValNat p (n - i).factorial - 1 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [dividedPowerFrobeniusCoefficient,
    padicValRat.div (mul_ne_zero (div_ne_zero (hf _) (hf _))
      (div_ne_zero (pow_ne_zero _ hp) (hf _))) hp,
    padicValRat.mul (div_ne_zero (hf _) (hf _)) (div_ne_zero (pow_ne_zero _ hp) (hf _)),
    padicValRat.div (hf _) (hf _), padicValRat.div (pow_ne_zero _ hp) (hf _)]
  simp only [padicValRat.of_nat, padicValRat.pow, padicValNat_self,
    padicValNat_factorial_mul]
  push_cast
  omega

/-- 正次数のFrobenius展開係数をpで割ってもp可積分。 -/
theorem dividedPowerFrobeniusCoefficient_valuation_nonneg (n i : ℕ)
    (hn : n ≠ 0) (hi : i ≤ n) :
    0 ≤ padicValRat p (dividedPowerFrobeniusCoefficient p n i) := by
  rw [dividedPowerFrobeniusCoefficient_valuation n i hi]
  have hb : padicValNat p (n - i).factorial < n := by
    by_cases h : n - i = 0
    · simpa [h] using Nat.pos_of_ne_zero hn
    · exact lt_of_lt_of_le (padicValNat_factorial_lt_of_ne_zero p h) (Nat.sub_le n i)
  omega

/-- 冪の展開係数のp進付値の正確な式。 -/
theorem dividedPowerPowerCoefficient_valuation (n : ℕ) :
    padicValRat p (dividedPowerPowerCoefficient p n) =
      (n : ℤ) - (p - 1 : ℕ) * padicValNat p n.factorial - 1 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [dividedPowerPowerCoefficient,
    padicValRat.div (hf _) (mul_ne_zero (pow_ne_zero _ (hf _)) hp),
    padicValRat.mul (pow_ne_zero _ (hf _)) hp]
  simp only [padicValRat.of_nat, padicValRat.pow, padicValNat_self,
    padicValNat_factorial_mul]
  have hp1 := (Fact.out : p.Prime).one_lt
  push_cast [Nat.cast_sub (Nat.one_le_of_lt hp1)]
  ring

/-- 正次数の冪の展開係数をpで割ってもp可積分。 -/
theorem dividedPowerPowerCoefficient_valuation_nonneg (n : ℕ) (hn : n ≠ 0) :
    0 ≤ padicValRat p (dividedPowerPowerCoefficient p n) := by
  rw [dividedPowerPowerCoefficient_valuation]
  have hb := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn
  have hb' : (((p - 1) * padicValNat p n.factorial : ℕ) : ℤ) < n := by
    exact_mod_cast hb
  push_cast at hb'
  omega

/-- 非負p進付値を持つ有理数の既約分母はpで割れない。 -/
theorem prime_not_dvd_den_of_padicVal_nonneg (q : ℚ) (hq : 0 ≤ padicValRat p q) :
    ¬p ∣ q.den := by
  have hd : padicValNat p q.den = 0 := by
    rcases q.num_or_den_zero_padicVal (Fact.out : p.Prime) with hnum | hden
    · rw [padicValRat_def, hnum] at hq
      omega
    · exact hden
  intro hdiv
  have hpos := one_le_padicValNat_of_dvd q.den_ne_zero hdiv
  omega

end SerrePositivity.BhattScholze
