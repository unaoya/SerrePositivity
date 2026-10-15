module

public import SerrePositivity.BhattScholze.RankOneDPAnyBasis
public import Mathlib.Tactic.Ring

/-! # p=0の係数環上の一元分冪基底の次数ブロック計算

零環も許し、CharPのインスタンスは要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]
local notation "DA" => DividedPowerAlgebra A A

/-- 一次生成元を掛けたときの全標準分冪生成元上の式。 -/
theorem rankOneDPGenerator_mul (n : ℕ) :
    DividedPowerAlgebra.dp A 1 (1 : A) * DividedPowerAlgebra.dp A n (1 : A) =
      (n + 1 : ℕ) * DividedPowerAlgebra.dp A (n + 1) (1 : A) := by
  simpa only [Nat.choose_one_right, Nat.add_comm, nsmul_eq_mul] using
    (DividedPowerAlgebra.dp_mul (R := A) (n := 1) (p := n) (m := (1 : A)))

/-- p=0なら、次数pk+rの基底への一次生成元の作用係数はr+1。 -/
theorem rankOneDPGenerator_mul_prime_block {p : ℕ} (hp : (p : A) = 0) (k r : ℕ) :
    DividedPowerAlgebra.dp A 1 (1 : A) * DividedPowerAlgebra.dp A (p * k + r) (1 : A) =
      (r + 1 : ℕ) * DividedPowerAlgebra.dp A (p * k + r + 1) (1 : A) := by
  rw [rankOneDPGenerator_mul]
  have hpD : (p : DA) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A DA) hp
  simp only [Nat.cast_add, Nat.cast_mul, hpD, zero_mul, zero_add]

/-- p=0なら、次数pkの生成元へのx^rの作用はr!倍の次数pk+rの生成元。 -/
theorem rankOneDPGenerator_pow_mul_prime_block {p : ℕ} (hp : (p : A) = 0) (k r : ℕ) :
    DividedPowerAlgebra.dp A 1 (1 : A) ^ r * DividedPowerAlgebra.dp A (p * k) (1 : A) =
      (r.factorial : DA) * DividedPowerAlgebra.dp A (p * k + r) (1 : A) := by
  induction r with
  | zero => simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, Nat.add_zero]
  | succ r ih =>
      calc
        _ = (r.factorial : DA) * (DividedPowerAlgebra.dp A 1 (1 : A) *
            DividedPowerAlgebra.dp A (p * k + r) (1 : A)) := by
          rw [pow_succ', mul_assoc, ih]
          ring
        _ = (r.factorial : DA) * ((r + 1 : ℕ) *
            DividedPowerAlgebra.dp A (p * k + r + 1) (1 : A)) := by
          rw [rankOneDPGenerator_mul_prime_block hp]
        _ = _ := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          simp only [Nat.add_assoc]
          ring

/-- 正のpが係数環で零なら、一次分冪生成元のp乗は零。 -/
theorem rankOneDPGenerator_pow_eq_zero {p : ℕ} (hpos : 0 < p) (hp : (p : A) = 0) :
    DividedPowerAlgebra.dp A 1 (1 : A) ^ p = 0 := by
  have hpD : (p : DA) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A DA) hp
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos le_rfl
  have hf : (p.factorial : DA) = 0 := by
    rw [hk, Nat.cast_mul, hpD, zero_mul]
  have h := rankOneDPGenerator_pow_mul_prime_block hp 0 p
  simpa only [Nat.mul_zero, Nat.zero_add, DividedPowerAlgebra.dp_zero, mul_one, hf,
    zero_mul] using h

end SerrePositivity.BhattScholze
