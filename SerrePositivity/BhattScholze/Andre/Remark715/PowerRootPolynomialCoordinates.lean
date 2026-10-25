module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomial
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# André E1・E2：小数指数ごとの通常多項式座標

## 概要

無限 p 冪根多項式環の元を、1 未満の小数指数で添字付けた有限個の通常多項式へ分解する。
BS Rem 7.15（著者版 p.62）のモニック冪商の自由基底の準備。

## 方針

単項式の指数を自然数部分と小数部分に分け、係数の有限台関数を curry する。
通常変数 Y₀ の多項式評価射も明示する。

## 規約

ここでは元の係数環上の線形同型を構成する。通常多項式環上の線形性は次工程で示す。
係数環の標数や非零性は不要。p は正とする。

## 使われ方

小数指数による通常多項式環上の自由基底とモニック冪商への移送に使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp
local notation "G" => powerRootExponentMonoid p hp
local notation "F" => PowerRootFraction p hp

/-- 概要：通常変数を Y₀ に送る、通常多項式環からの係数射。
方針：標準多項式評価代数射を使う。
規約：係数環 R の作用は元の加法モノイド環の作用を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の P/(fᵖ) の f の像。 -/
def powerRootPolynomialBaseMap : R[X] →ₐ[R] P :=
  Polynomial.aeval (powerRootPolynomialVariable R p hp 0)

/-- 概要：標準多項式評価射による通常多項式環上の代数構造。
方針：明示した係数射の toAlgebra を使う。
規約：他の多項式代数作用と混同しないよう局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の小数指数基底。 -/
@[instance_reducible] def powerRootPolynomialBaseAlgebra : Algebra R[X] P :=
  (powerRootPolynomialBaseMap R p hp).toRingHom.toAlgebra

/-- 概要：単項式は自然数部分ごとの通常多項式を小数指数で有限個並べる座標を持つ。
方針：指数の分解による添字の同値、curry、通常多項式の係数表示を合成する。
規約：この段階では元の R 上の線形同型。
使われ方：BS Rem 7.15（著者版 p.62）の明示的自由基底。 -/
def powerRootPolynomialCoordinates : P ≃ₗ[R] (F →₀ R[X]) := by
  let eP : R[X] ≃ₗ[R] (ℕ →₀ R) :=
    (Polynomial.toFinsuppIsoLinear R).trans (AddMonoidAlgebra.coeffLinearEquiv R)
  let eG := (powerRootExponentSplit p hp).trans (Equiv.prodComm ℕ F)
  exact (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.domLCongr eG).trans
      ((Finsupp.curryLinearEquiv R).trans (Finsupp.mapRange.linearEquiv eP.symm)))

/-- 概要：単項式の座標は、小数部分の成分の自然数部分の単項式となる。
方針：添字変更・curry・多項式係数表示を一項の有限台関数上で計算する。
規約：係数 a はそのまま保たれる。
使われ方：BS Rem 7.15（著者版 p.62）の通常変数作用との整合性。 -/
theorem powerRootPolynomialCoordinates_single (q : G) (a : R) :
    powerRootPolynomialCoordinates R p hp (AddMonoidAlgebra.single q a) =
      Finsupp.single (powerRootExponentSplit p hp q).2
        (Polynomial.monomial (powerRootExponentSplit p hp q).1 a) := by
  simp [powerRootPolynomialCoordinates, Finsupp.curry_single]
  rfl

/-- 概要：通常多項式の単項式は自然数指数の単項式に写る。
方針：Y₀ の指数が 1 であることと、単項式の冪の公式を使う。
規約：この公式は標準多項式係数射について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の通常変数の作用の照合。 -/
theorem powerRootPolynomialBaseMap_monomial (n : ℕ) (a : R) :
    powerRootPolynomialBaseMap R p hp (Polynomial.monomial n a) =
      AddMonoidAlgebra.single (powerRootNatExponent p hp n) a := by
  have he : n • powerRootVariableExponent p hp 0 = powerRootNatExponent p hp n := by
    apply Subtype.ext
    change n • (1 / (p : ℚ) ^ 0) = (n : ℚ)
    simp
  simp [powerRootPolynomialBaseMap, Polynomial.aeval_monomial,
    powerRootPolynomialVariable, AddMonoidAlgebra.single_pow, he]

end SerrePositivity.BhattScholze.Andre
