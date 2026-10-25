module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialStable
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing

/-! # 具体的階乗生成部分環のδ構造と分冪作用

元のAにはp正則性を課さず、局所化内の部分環のp正則性を直接使う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
local notation "L₀" => Localization.Away (p : A)
local notation "S₀" => pDivisionFactorialSubring p

/-- 元のAから具体的階乗生成部分環への実標準射。 -/
def pDivisionFactorialBase (p : ℕ) (y : σ → A) : A →+* pDivisionFactorialSubring p y :=
  (algebraMap A (Localization.Away (p : A))).codRestrict _ (pDivisionFactorialSubring_coeff_mem y)

/-- δ安定性により制限した、具体的階乗生成部分環のδ構造。 -/
def pDivisionFactorialDelta (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : σ → A) : DeltaStructure p (S₀ y) :=
  (deltaPDivisionAwayStructure D).subring (S₀ y) (pDivisionFactorialSubring_delta_mem hlocal D y)

/-- 具体的階乗生成部分環の局所化への包含はδ射。 -/
theorem pDivisionFactorialDelta_subtype_isDeltaHom
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    (pDivisionFactorialDelta hlocal D y).IsDeltaHom (deltaPDivisionAwayStructure D)
      (S₀ y).subtype :=
  (deltaPDivisionAwayStructure D).subring_subtype_isDeltaHom _ _

/-- 元のAからの実基底射もδ射。 -/
theorem pDivisionFactorialDelta_base_isDeltaHom
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    D.IsDeltaHom (pDivisionFactorialDelta hlocal D y) (pDivisionFactorialBase p y) := by
  intro a
  apply Subtype.ext
  exact deltaPDivisionAwayStructure_base_isDeltaHom D a

omit [Fact p.Prime] in
/-- pは局所化内で単元なので、階乗生成部分環内ではp正則。 -/
theorem pDivisionFactorial_p_mul_injective (y : σ → A) :
    Function.Injective (fun x : S₀ y ↦ (p : S₀ y) * x) := by
  have hp : IsUnit (p : L₀) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (S := L₀) (p : A)
  intro x z hxz
  apply Subtype.ext
  apply hp.mul_left_cancel
  exact congrArg (fun t : S₀ y ↦ (t : L₀)) hxz

/-- 具体的部分環のp除算可能イデアル上の既存の標準分冪構造。 -/
def pDivisionFactorialDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    DividedPowers (pDivisionFactorialDelta hlocal D y).primeDividedPowerIdeal :=
  (pDivisionFactorialDelta hlocal D y).primeDividedPowers (pDivisionFactorial_p_mul_injective y)
    (fun m hm ↦ by simpa only [map_natCast] using (hlocal m hm).map (pDivisionFactorialBase p y))

/-- 各基底元y_sは、この部分環のp除算可能イデアルに入る。 -/
theorem pDivisionFactorialBase_mem_primeIdeal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A)
    (y : σ → A) (s : σ) :
    pDivisionFactorialBase p y (y s) ∈
      (pDivisionFactorialDelta hlocal D y).primeDividedPowerIdeal := by
  apply ((pDivisionFactorialDelta hlocal D y).mem_primeDividedPowerIdeal _).mpr
  refine ⟨⟨IsLocalization.Away.invSelf (p : A) * (algebraMap A L₀ (y s)) ^ p,
    pDivisionFactorialSubring_pow_div_prime_mem y hlocal s⟩, ?_⟩
  apply Subtype.ext
  change (algebraMap A L₀ (y s)) ^ p = (p : L₀) *
    (IsLocalization.Away.invSelf (p : A) * (algebraMap A L₀ (y s)) ^ p)
  rw [← mul_assoc, ← map_natCast (algebraMap A L₀), IsLocalization.Away.mul_invSelf, one_mul]

/-- 実分冪作用の値は、局所化内の正規化された階乗分母と一致する。 -/
theorem pDivisionFactorialDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    ((pDivisionFactorialDividedPowers hlocal D y).dpow n
      (pDivisionFactorialBase p y (y s)) : L₀) = pDivisionFactorialValue p y s n := by
  have hu := DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)
  apply hu.mul_left_cancel
  change (n.factorial : L₀) * _ = (n.factorial : L₀) * (Ring.inverse _ * _)
  rw [Ring.mul_inverse_cancel_left _ _ hu]
  have h := (pDivisionFactorialDividedPowers hlocal D y).factorial_mul_dpow_eq_pow
    (pDivisionFactorialBase_mem_primeIdeal hlocal D y s) (n := n)
  exact congrArg (fun t : S₀ y ↦ (t : L₀)) h

end SerrePositivity.BhattScholze
