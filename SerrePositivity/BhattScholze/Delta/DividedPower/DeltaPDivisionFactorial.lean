module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaFactorialDivision
public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivision

/-! # raw φ(y)/p包の具体的な階乗分母

任意の元族を許し、正則性を要求しない。選んだ元の階乗を払った式を示す。
これだけでは分冪構造の公理・分冪包の普遍性を結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A)
local notation "a₀" => fun s ↦ D.frobeniusLift (y s)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "v₀" => deltaAdjoinDivisionVariable D (p : A) a₀

/-- rawφ除算包で、j(y_s)^p/pはv_s−j(δ(y_s))として存在する。 -/
theorem deltaPDivisionRaw_prime_dvd_pow (s : σ) : (p : B₀) ∣ j₀ (y s) ^ p := by
  have hp : j₀ (p : A) = (p : B₀) := map_natCast j₀ p
  have h := deltaAdjoinDivision_relation D (p : A) a₀ s
  rw [hp] at h
  refine ⟨v₀ s - j₀ (D.delta (y s)), ?_⟩
  calc
    j₀ (y s) ^ p = j₀ (D.frobeniusLift (y s)) - (p : B₀) * j₀ (D.delta (y s)) := by
      rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp]
      ring
    _ = (p : B₀) * (v₀ s - j₀ (D.delta (y s))) := by
      change j₀ (a₀ s) - _ = _
      rw [← h, mul_sub]

/-- 非p倍の自然数がAの単元なら、raw包のj(y_s)は全階乗で除算できる。 -/
theorem deltaPDivisionRaw_factorial_dvd_pow
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) :
    (n.factorial : B₀) ∣ j₀ (y s) ^ n := by
  apply (E₀).factorial_dvd_pow_of_prime_dvd_pow
    (fun m hm ↦ by simpa only [map_natCast] using (hlocal m hm).map j₀)
    (deltaPDivisionRaw_prime_dvd_pow D y s)

/-- raw包内に選んだj(y_s)^n/n!。正則性なしでは分母を払う式で指定する。 -/
def deltaPDivisionRawFactorialQuotient
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) : B₀ :=
  (deltaPDivisionRaw_factorial_dvd_pow D y hlocal s n).choose

/-- 選んだ元はn!を掛けるとj(y_s)^nに戻る。 -/
theorem deltaPDivisionRawFactorialQuotient_spec
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) :
    (n.factorial : B₀) * deltaPDivisionRawFactorialQuotient D y hlocal s n =
      j₀ (y s) ^ n :=
  (deltaPDivisionRaw_factorial_dvd_pow D y hlocal s n).choose_spec.symm

/-- 0番目の階乗分母は1。 -/
theorem deltaPDivisionRawFactorialQuotient_zero
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) :
    deltaPDivisionRawFactorialQuotient D y hlocal s 0 = 1 := by
  simpa using deltaPDivisionRawFactorialQuotient_spec D y hlocal s 0

/-- 1番目の階乗分母は元の基底元。 -/
theorem deltaPDivisionRawFactorialQuotient_one
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) :
    deltaPDivisionRawFactorialQuotient D y hlocal s 1 = j₀ (y s) := by
  simpa using deltaPDivisionRawFactorialQuotient_spec D y hlocal s 1

end SerrePositivity.BhattScholze
