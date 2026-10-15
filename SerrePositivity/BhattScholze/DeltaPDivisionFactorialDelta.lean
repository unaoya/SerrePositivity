module

public import SerrePositivity.BhattScholze.DeltaDividedPowerExpansion
public import SerrePositivity.BhattScholze.DeltaDividedPowerCoefficientImage
public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialSubring

/-! # 実局所化δ構造での階乗生成元の展開

環同型に沿った別のδ作用ではなく、既存の局所化δ作用を直接計算する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
local notation "L₀" => Localization.Away (p : A)

/-- 局所化内のRing.inverseによる分母は、既存ℚ作用による1/n!に等しい。 -/
theorem pDivisionFactorialValue_eq_rat (y : σ → A) (s : σ) (n : ℕ) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    pDivisionFactorialValue p y s n =
      algebraMap ℚ L₀ (1 / (n.factorial : ℚ)) * (algebraMap A L₀ (y s)) ^ n := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  have hu : IsUnit (n.factorial : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have he := hu.map_ringInverse (algebraMap ℚ L₀)
  rw [Ring.inverse_eq_inv, map_natCast] at he
  change Ring.inverse _ * _ = _
  rw [one_div, he]

/-- 実局所化のFrobeniusは階乗生成元に通常のφ(y)=y^p+pδ(y)を適用する。 -/
theorem pDivisionFactorialValue_frobeniusLift (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    (deltaPDivisionAwayStructure D).frobeniusLift (pDivisionFactorialValue p y s n) =
      algebraMap ℚ L₀ (1 / (n.factorial : ℚ)) *
        ((algebraMap A L₀ (y s)) ^ p + (p : L₀) * algebraMap A L₀ (D.delta (y s))) ^ n := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  rw [pDivisionFactorialValue_eq_rat hlocal, map_mul, map_pow, RingHom.map_rat_algebraMap]
  rw [DeltaStructure.frobeniusLift_apply,
    ← deltaPDivisionAwayStructure_base_isDeltaHom D (y s)]

/-- 実局所化でのδ(γ_n(y_s))を、p可積分係数と階乗分母の有限和で書く。 -/
theorem pDivisionFactorialValue_delta_expansion (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    (deltaPDivisionAwayStructure D).delta (pDivisionFactorialValue p y s n) =
      (∑ i ∈ Finset.range (n + 1),
        algebraMap ℚ L₀ (dividedPowerFrobeniusCoefficient p n i) *
          pDivisionFactorialValue p y s (p * i) * (algebraMap A L₀ (D.delta (y s))) ^ (n - i)) -
      algebraMap ℚ L₀ (dividedPowerPowerCoefficient p n) *
        pDivisionFactorialValue p y s (p * n) := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let f := algebraMap ℚ L₀
  let E := deltaPDivisionAwayStructure D
  let c := pDivisionFactorialValue p y s n
  let x := algebraMap A L₀ (y s)
  let z := algebraMap A L₀ (D.delta (y s))
  have hpinv : f (1 / (p : ℚ)) * (p : L₀) = 1 := by
    have he : (1 / (p : ℚ)) * (p : ℚ) = 1 := by
      exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    simpa only [map_mul, map_natCast, map_one] using congrArg f he
  have hd : E.delta c = f (1 / (p : ℚ)) * (E.frobeniusLift c - c ^ p) := by
    rw [E.frobeniusLift_apply, add_sub_cancel_left, ← mul_assoc, hpinv, one_mul]
  have hs : f (1 / (p : ℚ)) * f (1 / (n.factorial : ℚ)) =
      f (1 / ((p : ℚ) * (n.factorial : ℚ))) := by
    rw [← map_mul, one_div_mul_one_div]
  have hF : f (1 / (p : ℚ)) * E.frobeniusLift c =
      ∑ i ∈ Finset.range (n + 1), f (dividedPowerFrobeniusCoefficient p n i) *
        pDivisionFactorialValue p y s (p * i) * z ^ (n - i) := by
    rw [pDivisionFactorialValue_frobeniusLift hlocal D, ← mul_assoc, hs]
    simpa only [map_natCast, pDivisionFactorialValue_eq_rat hlocal] using
      (dividedPower_frobenius_expansion (p := p) f x z n)
  have hP : f (1 / (p : ℚ)) * c ^ p =
      f (dividedPowerPowerCoefficient p n) * pDivisionFactorialValue p y s (p * n) := by
    dsimp only [c]
    simpa only [pDivisionFactorialValue_eq_rat hlocal] using
      (dividedPower_power_expansion (p := p) f x n)
  rw [hd, mul_sub, hF, hP]


include hlocal in
/-- 各階乗生成元の実δ像は、具体的な階乗生成部分環に入る。 -/
theorem pDivisionFactorialValue_delta_mem (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    (deltaPDivisionAwayStructure D).delta (pDivisionFactorialValue p y s n) ∈
      pDivisionFactorialSubring p y := by
  by_cases hn : n = 0
  · subst n
    have he : pDivisionFactorialValue p y s 0 = 1 := by simp [pDivisionFactorialValue]
    rw [he, DeltaStructure.delta_one]
    exact (pDivisionFactorialSubring p y).zero_mem
  · let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    rw [pDivisionFactorialValue_delta_expansion hlocal D]
    apply (pDivisionFactorialSubring p y).sub_mem
    · apply (pDivisionFactorialSubring p y).sum_mem
      intro i hi
      apply (pDivisionFactorialSubring p y).mul_mem
      · apply (pDivisionFactorialSubring p y).mul_mem
        · obtain ⟨a, ha⟩ := dividedPowerFrobeniusCoefficient_mem_baseRange hlocal n i hn
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          rw [← ha]
          exact pDivisionFactorialSubring_coeff_mem y a
        · exact pDivisionFactorialSubring_value_mem y s (p * i)
      · exact (pDivisionFactorialSubring p y).pow_mem
          (pDivisionFactorialSubring_coeff_mem y (D.delta (y s))) _
    · apply (pDivisionFactorialSubring p y).mul_mem
      · obtain ⟨a, ha⟩ := dividedPowerPowerCoefficient_mem_baseRange hlocal n hn
        rw [← ha]
        exact pDivisionFactorialSubring_coeff_mem y a
      · exact pDivisionFactorialSubring_value_mem y s (p * n)

end SerrePositivity.BhattScholze
