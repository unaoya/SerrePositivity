module

public import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Flat.Localization

/-!
# p 局所整数上の平坦性

## 概要
p 正則な p 局所環は ℤ₍ₚ₎ 上平坦。

## 方針
零でない整数を p の冪と p と互いに素な因子に分け、整数上のねじれなしを示す。

## 規約
BS 著者版 Lemma 2.38 の係数環。

## 使われ方
原典の多項式環上の Tor を、係数を拡大した多項式環上で計算する。
-/

public noncomputable section

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Algebra (PrimeLocalInt p) A]

/-- 概要：p 局所かつ p 正則な係数環は p 局所整数上平坦。
方針：非零整数の p 冪部分と可逆部分で、整数上のねじれがないことを示す。
規約：BS 著者版 Lemma 2.38 の係数環。
使われ方：分冪包の多項式環上の Tor の底変換。 -/
theorem primeLocalInt_moduleFlat (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hp : IsSMulRegular A (p : A)) : Module.Flat (PrimeLocalInt p) A := by
  have hnat (n : ℕ) (hn : n ≠ 0) (x : A) (hx : (n : A) * x = 0) : x = 0 := by
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow] at hx
    apply (hlocal m hm).mul_left_cancel
    apply (hp.pow k)
    change (p : A)^k * ((m : A) * x) = (p : A)^k * ((m : A) * 0)
    simpa only [← mul_assoc, mul_zero] using hx
  haveI : Module.IsTorsionFree ℤ A := Module.IsTorsionFree.of_smul_eq_zero fun z x hx => by
    rw [zsmul_eq_mul] at hx
    cases z with
    | ofNat n =>
      by_cases hn : n = 0
      · exact Or.inl (by simp [hn])
      · change ((n : ℤ) : A) * x = 0 at hx
        exact Or.inr (hnat n hn x (by simpa only [Int.cast_natCast] using hx))
    | negSucc n =>
      right
      apply hnat (n + 1) (Nat.succ_ne_zero n) x
      simpa only [Int.cast_negSucc, ← Nat.cast_succ, neg_mul, neg_eq_zero] using hx
  letI : Module ℤ A := Algebra.toModule
  letI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := PrimeLocalInt p) (A := A)
    (Subsingleton.elim _ _)
  exact (Module.flat_iff_of_isLocalization (PrimeLocalInt p)
    (Ideal.span {(p : ℤ)}).primeCompl A).2 inferInstance

end SerrePositivity.BhattScholze
