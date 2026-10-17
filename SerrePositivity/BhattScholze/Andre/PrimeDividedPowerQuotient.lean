module

public import SerrePositivity.BhattScholze.DeltaDividedPowers
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-!
# André E1・E2：p 局所・p 正則環の分冪構造の mod p 降下

## 概要

p 局所かつ p 正則な環の分冪イデアルが p を含めば、(p) は分冪で保たれ、
その分冪構造は mod p 商へ降りる。BS Rem 7.15(1)（著者版 p.62）の
階乗部分環の剰余から実分冪構造を構成するための補題。

## 方針

n! の p 付値が正の n より小さいことと階乗恒等式により、γₙ(p) の p 可除性を得る。
生成イデアルの分冪安定性と既存の商の分冪 API を使う。

## 規約

係数環に分冪構造そのものを明示引数として与える。新たな引用は使わない。

## 使われ方

階乗部分環の大きい分冪イデアルを mod p へ降ろし、正次数イデアルの像へ制限する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
variable {I : Ideal A} (H : DividedPowers I)

/-- 概要：p 正則・p 局所環の分冪イデアル内の p の正次数分冪は p で割り切れる。
方針：階乗の p 冪因子を正則性で消去し、残りの単元因子を除く。
規約：分冪イデアルへの p の所属を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の剰余への降下。 -/
theorem dividedPower_prime_dvd
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I)
    (n : ℕ) (hn : n ≠ 0) : (p : A) ∣ H.dpow n (p : A) := by
  obtain ⟨k, m, hm, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.factorial_ne_zero n) p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := fun hm0 => hm (hm0 ▸ dvd_zero p)
  have hk : padicValNat p n.factorial = k := by
    rw [hfac, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hkn : k < n := hk ▸ padicValNat_factorial_lt_of_ne_zero p hn
  have hr : IsLeftRegular (p : A) := hpA
  have he : (m : A) * H.dpow n (p : A) = (p : A) ^ (n - k) := by
    apply hr.pow k
    calc
      (p : A) ^ k * ((m : A) * H.dpow n (p : A)) =
          (n.factorial : A) * H.dpow n (p : A) := by
            rw [hfac, Nat.cast_mul, Nat.cast_pow, mul_assoc]
      _ = (p : A) ^ n := H.factorial_mul_dpow_eq_pow hpI
      _ = (p : A) ^ k * (p : A) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn.le]
  obtain ⟨v, hv⟩ := hlocal m hm
  have he' : H.dpow n (p : A) = (v⁻¹ : Aˣ) * (p : A) ^ (n - k) := by
    rw [← he, ← hv]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  rw [he']
  exact dvd_mul_of_dvd_right (dvd_pow_self (p : A) (Nat.sub_ne_zero_of_lt hkn)) _

/-- 概要：p を含む分冪イデアル内では (p) は分冪で保たれる。
方針：主イデアルの分冪安定性を生成元 p 上で確認する。
規約：p 正則性と p 局所性を前提に残す。
使われ方：BS Rem 7.15(1)（著者版 p.62）の mod p 分冪商の入力。 -/
theorem dividedPower_span_prime_isSubDPIdeal
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I) :
    H.IsSubDPIdeal (Ideal.span {(p : A)}) := by
  apply (H.span_isSubDPIdeal_iff (Set.singleton_subset_iff.mpr hpI)).mpr
  intro n hn s hs
  rcases hs with rfl
  exact Ideal.mem_span_singleton.mpr (dividedPower_prime_dvd p H hpA hlocal hpI n hn)

/-- 概要：p を含む分冪イデアルの構造は実 mod p 商へ降りる。
方針：(p) の分冪安定性から商 API に必要な交わりの安定性を得る。
規約：対象イデアルは元の分冪イデアルの商への像そのもの。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正標数の実分冪構造。 -/
def dividedPowerModPrime
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I) :
    DividedPowers (I.map (Ideal.Quotient.mk (Ideal.span {(p : A)}))) := by
  have hsub := dividedPower_span_prime_isSubDPIdeal p H hpA hlocal hpI
  apply DividedPowers.Quotient.dividedPowers H
  simpa only [inf_eq_left.mpr hsub.isSubideal] using hsub

/-- 概要：mod p の分冪作用は元の分冪値を標準商射で送った値に一致する。
方針：商分冪構造の評価公式を適用する。
規約：元は元の分冪イデアル内に取る。
使われ方：BS Rem 7.15(1)（著者版 p.62）の階乗生成元の剰余の照合。 -/
theorem dividedPowerModPrime_apply
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I)
    (n : ℕ) {a : A} (ha : a ∈ I) :
    (dividedPowerModPrime p H hpA hlocal hpI).dpow n
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) =
      Ideal.Quotient.mk _ (H.dpow n a) := by
  exact DividedPowers.Quotient.dpow_apply H
    (by
      have hsub := dividedPower_span_prime_isSubDPIdeal p H hpA hlocal hpI
      simpa only [inf_eq_left.mpr hsub.isSubideal] using hsub) ha


/-- 概要：標準 mod p 商射は分冪射である。
方針：商分冪構造の射の互換性を使う。
規約：元の分冪イデアルとその実像を比較する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数イデアルの像への制限。 -/
theorem dividedPowerModPrime_isDPMorphism
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hpI : (p : A) ∈ I) :
    H.IsDPMorphism (dividedPowerModPrime p H hpA hlocal hpI)
      (Ideal.Quotient.mk (Ideal.span {(p : A)})) := by
  exact DividedPowers.Quotient.isDPMorphism H
    (by
      have hsub := dividedPower_span_prime_isSubDPIdeal p H hpA hlocal hpI
      simpa only [inf_eq_left.mpr hsub.isSubideal] using hsub)

end SerrePositivity.BhattScholze.Andre
