module

public import SerrePositivity.BhattScholze.DeltaDividedPowerCoefficients
public import SerrePositivity.BhattScholze.DeltaDividedPowers

/-! # 分冪展開のp可積分係数の実基底像

既約分母の単元逆数をA内で取り、標準局所化像の式を証明する。
ℚ作用は前工程の既存のものを用いる。p正則性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 非負p進付値の有理数の標準局所化像は、p局所環Aの基底像に入る。 -/
theorem primeLocalRat_mem_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (q : ℚ)
    (hq : 0 ≤ padicValRat p q) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    algebraMap ℚ (Localization.Away (p : A)) q ∈
      (algebraMap A (Localization.Away (p : A))).range := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let L := Localization.Away (p : A)
  let f := algebraMap A L
  obtain ⟨v, hv⟩ := hlocal q.den (prime_not_dvd_den_of_padicVal_nonneg q hq)
  refine ⟨(v⁻¹ : Aˣ) * (q.num : A), ?_⟩
  have hdQ : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hqQ : (q.den : ℚ) * q = (q.num : ℚ) := by
    have h := (div_eq_iff hdQ).mp q.num_div_den
    simpa only [mul_comm] using h.symm
  have hqL := congrArg (algebraMap ℚ L) hqQ
  simp only [map_mul, map_natCast, map_intCast] at hqL
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal q.den q.den_ne_zero).mul_left_cancel
  calc
    (q.den : L) * f ((v⁻¹ : Aˣ) * (q.num : A)) =
        f ((q.den : A) * ((v⁻¹ : Aˣ) * (q.num : A))) := by simp only [map_mul, map_natCast]
    _ = f (q.num : A) := by rw [← hv, Units.mul_inv_cancel_left]
    _ = (q.den : L) * algebraMap ℚ L q := by rw [map_intCast, hqL]

/-- 正次数のFrobenius分冪展開係数の像はAの実標準像に入る。 -/
theorem dividedPowerFrobeniusCoefficient_mem_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (n i : ℕ)
    (hn : n ≠ 0) (hi : i ≤ n) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    algebraMap ℚ (Localization.Away (p : A)) (dividedPowerFrobeniusCoefficient p n i) ∈
      (algebraMap A (Localization.Away (p : A))).range :=
  primeLocalRat_mem_baseRange hlocal _
    (dividedPowerFrobeniusCoefficient_valuation_nonneg n i hn hi)

/-- 正次数の冪の分冪展開係数の像もAの実標準像に入る。 -/
theorem dividedPowerPowerCoefficient_mem_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (n : ℕ) (hn : n ≠ 0) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    algebraMap ℚ (Localization.Away (p : A)) (dividedPowerPowerCoefficient p n) ∈
      (algebraMap A (Localization.Away (p : A))).range :=
  primeLocalRat_mem_baseRange hlocal _ (dividedPowerPowerCoefficient_valuation_nonneg n hn)

end SerrePositivity.BhattScholze
