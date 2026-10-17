module

public import SerrePositivity.BhattScholze.Andre.PrimeDividedPowerQuotient
public import SerrePositivity.BhattScholze.RegularPrincipalDPUniversal

/-!
# André E1・E2：階乗部分環の正次数イデアルの実 mod p 分冪構造

## 概要

p 局所 δ 係数環の階乗部分環を mod p に還元した環で、正次数の階乗生成元の
像のイデアルに実際の分冪構造を構成する。BS Rem 7.15(1)（著者版 p.62）。

## 方針

大きい p 除算可能イデアルの分冪構造を mod p に降ろし、正次数イデアルの像へ制限する。

## 規約

係数環の p 正則性や入力元の正則性はこの段階では不要。
階乗部分環自体の p 正則性を使用する。

## 使われ方

正則一元入力では既存の実 mod p 比較で一次関係商へ移し、実 pd 包と比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A)
local notation "S" => pDivisionFactorialSubring p y
local notation "E" => pDivisionFactorialDelta hlocal D y
local notation "H" => pDivisionFactorialDividedPowers hlocal D y
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : S)})

include hlocal in
omit [Fact p.Prime] in
/-- 概要：階乗部分環も p 局所である。
方針：元の係数環の単元を標準基底射で送る。
規約：p と互いに素な自然数を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の mod p 分冪降下への入力。 -/
theorem factorialSubring_primeLocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : S) := by
  simpa only [map_natCast] using (hlocal m hm).map (pDivisionFactorialBase p y)

/-- 概要：階乗部分環の p は大きい p 除算可能イデアルに属する。
方針：p がその p 乗を割ることを使う。
規約：正次数の階乗イデアルに p の所属を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の大きいイデアルからの降下。 -/
theorem factorialSubring_prime_mem : (p : S) ∈ (E).primeDividedPowerIdeal :=
  ((E).mem_primeDividedPowerIdeal _).mpr (dvd_pow_self _ (Fact.out : p.Prime).ne_zero)

/-- 概要：階乗部分環の大きい分冪構造は実 mod p 商へ降りる。
方針：階乗部分環の p 正則性・p 局所性と p の所属を一般降下補題へ渡す。
規約：対象は大きい分冪イデアルの標準商への実像。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数への制限の出発点。 -/
def factorialModPrimeAmbientDividedPowers :
    DividedPowers ((E).primeDividedPowerIdeal.map q) :=
  dividedPowerModPrime p H (pDivisionFactorial_p_mul_injective y)
    (factorialSubring_primeLocal hlocal y) (factorialSubring_prime_mem hlocal D y)

/-- 概要：mod p 正次数イデアルは、大きい分冪イデアル内で分冪に安定。
方針：元の正次数イデアルの安定性を分冪商射で送る。
規約：正次数イデアルの像をそのまま使い、飽和性を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数分冪構造の構成。 -/
theorem factorialModPrimeIdeal_isSubDPIdeal :
    (factorialModPrimeAmbientDividedPowers hlocal D y).IsSubDPIdeal
      ((pDivisionFactorialIdeal p y).map q) :=
  DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal
    (dividedPowerModPrime_isDPMorphism p H (pDivisionFactorial_p_mul_injective y)
      (factorialSubring_primeLocal hlocal y) (factorialSubring_prime_mem hlocal D y))
    (pDivisionFactorialIdeal_isSubDPIdeal hlocal D y)

/-- 概要：正次数の階乗イデアルの mod p 像には実際の分冪構造がある。
方針：大きい商分冪構造を分冪安定な正次数イデアルの像へ制限する。
規約：入力元の正則性と係数環の p 正則性は要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正標数での実分冪構造。 -/
def factorialModPrimeDividedPowers : DividedPowers ((pDivisionFactorialIdeal p y).map q) := by
  classical
  exact DividedPowers.IsSubDPIdeal.dividedPowers (factorialModPrimeAmbientDividedPowers hlocal D y)
    (factorialModPrimeIdeal_isSubDPIdeal hlocal D y)

/-- 概要：mod p の正次数分冪は元の大きい分冪作用の商像と一致する。
方針：正次数への制限と商分冪作用の二つの評価公式を使う。
規約：元を元の正次数イデアル内に取る。
使われ方：BS Rem 7.15(1)（著者版 p.62）の階乗生成元の比較。 -/
theorem factorialModPrimeDividedPowers_apply (n : ℕ) {a : S}
    (ha : a ∈ pDivisionFactorialIdeal p y) :
    (factorialModPrimeDividedPowers hlocal D y).dpow n (q a) = q ((H).dpow n a) := by
  classical
  rw [factorialModPrimeDividedPowers, DividedPowers.IsSubDPIdeal.dpow_eq_of_mem _ _
    (Ideal.mem_map_of_mem q ha)]
  exact dividedPowerModPrime_apply p H (pDivisionFactorial_p_mul_injective y)
    (factorialSubring_primeLocal hlocal y) (factorialSubring_prime_mem hlocal D y) n
    ((pDivisionFactorialIdeal_isSubDPIdeal hlocal D y).isSubideal ha)

/-- 概要：基底元 y_s の mod p 像の n 次分冪は n 次階乗生成元の mod p 像。
方針：降下前の具体的な階乗値の公式を商へ移す。
規約：n=0 も含める。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 包の標準生成元の照合。 -/
theorem factorialModPrimeDividedPowers_base_apply (s : σ) (n : ℕ) :
    (factorialModPrimeDividedPowers hlocal D y).dpow n
      (q (pDivisionFactorialBase p y (y s))) =
      q (⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ : S) := by
  rw [factorialModPrimeDividedPowers_apply hlocal D y n
    (pDivisionFactorialBase_mem_factorialIdeal y s)]
  congr 1
  apply Subtype.ext
  exact pDivisionFactorialDividedPowers_base_apply hlocal D y s n

end SerrePositivity.BhattScholze.Andre
