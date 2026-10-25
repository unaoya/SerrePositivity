module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPPrimeBlocks
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # p=0の係数環上の実次数ブロック基底

基底は係数環A上の基底であり、切断多項式環上の自由性はまだ主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]

/-- 素数pが零となる係数環では、p未満の次数の階乗が単元。零環も含む。 -/
theorem rankOneDPPrimeBlock_factorial_isUnit (hprime : p.Prime) (hp : (p : A) = 0)
    {r : ℕ} (hr : r < p) : IsUnit (r.factorial : A) := by
  have hnot : ¬p ∣ r.factorial := fun h ↦ (Nat.not_le_of_lt hr) (hprime.dvd_factorial.mp h)
  have hc : IsCoprime (p : A) (r.factorial : A) :=
    ((hprime.coprime_iff_not_dvd).mpr hnot).cast
  rw [hp] at hc
  exact isCoprime_zero_left.mp hc

/-- x^rγ_(pk)を全基底元とする、ℕ×Fin pで添字付けた実A加群基底。 -/
def rankOneDPPrimeBlockBasis (hprime : p.Prime) (hp : (p : A) = 0) :
    Module.Basis (ℕ × Fin p) A (DividedPowerAlgebra A A) := by
  letI : NeZero p := ⟨hprime.ne_zero⟩
  exact ((rankOneDPAnyBasis A).reindex (Nat.divModEquiv p)).isUnitSMul
    (w := fun z : ℕ × Fin p ↦ ((z.2 : ℕ).factorial : A))
    (fun z ↦ rankOneDPPrimeBlock_factorial_isUnit hprime hp z.2.is_lt)

/-- 実ブロック基底の各元は、指定されたx^rγ_(pk)に一致する。 -/
theorem rankOneDPPrimeBlockBasis_apply (hprime : p.Prime) (hp : (p : A) = 0)
    (k : ℕ) (r : Fin p) :
    rankOneDPPrimeBlockBasis hprime hp (k, r) =
      DividedPowerAlgebra.dp A 1 (1 : A) ^ (r : ℕ) *
        DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  dsimp only [rankOneDPPrimeBlockBasis]
  rw [Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply, rankOneDPAnyBasis_apply]
  change (r.val.factorial : A) • DividedPowerAlgebra.dp A (k * p + r.val) (1 : A) = _
  rw [Nat.mul_comm k p]
  simpa only [Algebra.smul_def, map_natCast] using
    (rankOneDPGenerator_pow_mul_prime_block hp k r.val).symm

/-- 一次生成元は、各ブロックの内部で次の基底元へ進める。 -/
theorem rankOneDPPrimeBlockBasis_mul (hprime : p.Prime) (hp : (p : A) = 0)
    (k : ℕ) (r : Fin p) (hr : r.val + 1 < p) :
    DividedPowerAlgebra.dp A 1 (1 : A) * rankOneDPPrimeBlockBasis hprime hp (k, r) =
      rankOneDPPrimeBlockBasis hprime hp (k, ⟨r.val + 1, hr⟩) := by
  rw [rankOneDPPrimeBlockBasis_apply, rankOneDPPrimeBlockBasis_apply, pow_succ', mul_assoc]

/-- 一次生成元は、各ブロックの最後の基底元を零へ送る。 -/
theorem rankOneDPPrimeBlockBasis_last_mul (hprime : p.Prime) (hp : (p : A) = 0)
    (k : ℕ) (r : Fin p) (hr : r.val + 1 = p) :
    DividedPowerAlgebra.dp A 1 (1 : A) * rankOneDPPrimeBlockBasis hprime hp (k, r) = 0 := by
  rw [rankOneDPPrimeBlockBasis_apply, ← mul_assoc, ← pow_succ', hr,
    rankOneDPGenerator_pow_eq_zero hprime.pos hp, zero_mul]

end SerrePositivity.BhattScholze
