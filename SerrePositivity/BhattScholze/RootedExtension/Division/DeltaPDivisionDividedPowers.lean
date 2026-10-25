module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorial
public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaDividedPowers
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionRawEmbedding

/-! # rawφ除算包の分冪構造と既存の階乗分母

正則一元入力の仮定を明示する。分冪包の普遍性・CFFは別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "ys" => fun _ : σ ↦ y
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀

/-- rawφ除算包の各基底元j(y)は実際にp除算可能イデアルに属する。 -/
theorem deltaPDivisionRaw_base_mem_primeDividedPowerIdeal (s : σ) :
    j₀ y ∈ (E₀).primeDividedPowerIdeal :=
  ((E₀).mem_primeDividedPowerIdeal _).mpr (deltaPDivisionRaw_prime_dvd_pow D ys s)

variable [Unique σ]
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))

/-- 正則一元raw包のp除算可能イデアル上の実際の分冪構造。 -/
def deltaPDivisionRawDividedPowers : DividedPowers (E₀).primeDividedPowerIdeal :=
  (E₀).primeDividedPowers (deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy)
    (fun m hm ↦ by simpa only [map_natCast] using (hlocal m hm).map j₀)

include hpA hg hv hy hlocal in
/-- raw包の実分冪作用は、前工程の具体的な階乗分母に一致する。 -/
theorem deltaPDivisionRawDividedPowers_eq_factorialQuotient (s : σ) (n : ℕ) :
    (deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).dpow n (j₀ y) =
      deltaPDivisionRawFactorialQuotient D ys hlocal s n := by
  let f := deltaPDivisionToAway D a₀
  apply deltaPDivisionRawToAway_injective (σ := σ) D y hpA hg v hv hy
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  calc
    (n.factorial : Localization.Away (p : A)) * f
        ((deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).dpow n (j₀ y)) =
      f ((n.factorial : B₀) *
        (deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).dpow n (j₀ y)) := by
          rw [map_mul, map_natCast]
    _ = f ((j₀ y) ^ n) := congrArg f
      ((deltaPDivisionRawDividedPowers D y hpA hg v hv hy hlocal).factorial_mul_dpow_eq_pow
        (deltaPDivisionRaw_base_mem_primeDividedPowerIdeal D y s))
    _ = f ((n.factorial : B₀) * deltaPDivisionRawFactorialQuotient D ys hlocal s n) :=
      congrArg f (deltaPDivisionRawFactorialQuotient_spec D ys hlocal s n).symm
    _ = (n.factorial : Localization.Away (p : A)) *
        f (deltaPDivisionRawFactorialQuotient D ys hlocal s n) := by
          rw [map_mul, map_natCast]

end SerrePositivity.BhattScholze
