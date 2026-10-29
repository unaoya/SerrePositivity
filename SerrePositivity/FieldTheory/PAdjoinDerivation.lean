module

public import SerrePositivity.FieldTheory.PAdjoin
public import SerrePositivity.FieldTheory.AdjoinSingletonDerivation
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # p 乗根の添加の導分

概要：p 乗根 `x`（`x ^ p = a`、`x` は底体に属さない）が拡大全体を生成するとき、二種類の導分を与える。
- `primeRootDerivation`：`x` を1に送る底体上の導分。
- `primeRootDerivationExtension`：`δ a = 0` を満たす導分 `δ` の、`x` を零に送る延長。
方針：最小多項式は `X ^ p - a` で、その微分は零。どちらも `adjoinSingletonDerivation`（一元生成の拡大への
延長の一般定理）の系として、両立条件 `f^δ(x) + f'(x) • v = 0` を確かめて定義する。
使われ方：p 基底の偏導分（`PBasisComplement`・`PBasisDifferentials`）、指数1の拡大の定数
（`ExponentOneDifferentialConstants`）、p 乗根の添加での微分の推移列の核（`PrimeRootDifferentialRank`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial

section Derivation

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem derivative_minpoly_eq_zero_of_prime_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) : derivative (minpoly F x) = 0 := by
  let : CharP F p := (algebraMap F K).charP (algebraMap F K).injective p
  rw [minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx]
  simp [derivative_X_pow]

/-- 一つの p 乗根 `x`（`x ^ p = a`、`x ∉ F`）が全体を生成するとき、`x` を1に送る `F` 上の導分。 -/
def primeRootDerivation
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) (hs : Algebra.adjoin F {x} = ⊤) :
    Derivation F K K :=
  adjoinSingletonDerivation (R := F) x hs 0 1 (by
    have h0 : (0 : Derivation F F K).mapCoeffs (minpoly F x) = 0 := by
      ext n
      simp
    simp [adjoinSingletonObstruction, coefficientEvalLinearMap, h0,
      derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx])

@[simp] theorem primeRootDerivation_self
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) (hs : Algebra.adjoin F {x} = ⊤) :
    primeRootDerivation x a hpow hx hs x = 1 :=
  adjoinSingletonDerivation_self ..

end Derivation

section Extension

variable {R K L V : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [AddCommGroup V] [Module R V] [Module K V] [Module L V]
  [IsScalarTower R K V] [IsScalarTower R L V] [IsScalarTower K L V]
variable {p : ℕ} [Fact p.Prime] [CharP L p]

/-- 非自明なp乗根 `x`（`x ^ p = a`）が終域を生成するとき、`δ a = 0` を満たす導分 `δ` の、
`x` を零に送る延長。 -/
def primeRootDerivationExtension (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) (δ : Derivation R K V) (hδa : δ a = 0) :
    Derivation R L V :=
  adjoinSingletonDerivation x hs δ 0 (by
    rw [adjoinSingletonObstruction, smul_zero, add_zero,
      minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx, map_sub, coefficientEvalLinearMap_C, hδa,
      sub_zero, ← monomial_one_right_eq_X_pow]
    simp [coefficientEvalLinearMap])

@[simp] theorem primeRootDerivationExtension_algebraMap (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) (δ : Derivation R K V) (hδa : δ a = 0) (c : K) :
    primeRootDerivationExtension x a hpow hx hs δ hδa (algebraMap K L c) = δ c :=
  adjoinSingletonDerivation_algebraMap ..

@[simp] theorem primeRootDerivationExtension_self (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) (δ : Derivation R K V) (hδa : δ a = 0) :
    primeRootDerivationExtension x a hpow hx hs δ hδa x = 0 :=
  adjoinSingletonDerivation_self ..

end Extension

end SerrePositivity
