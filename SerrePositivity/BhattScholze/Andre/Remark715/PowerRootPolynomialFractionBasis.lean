module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPolynomialCoordinates
public import Mathlib.Algebra.Polynomial.Inductions

/-!
# André E1・E2：通常多項式環上の小数指数基底

## 概要

無限 p 冪根多項式環は、通常変数を Y₀ に送る多項式環上で自由であり、
1 未満の p 冪分母指数の単項式が基底となる。
BS Rem 7.15（著者版 p.62）のモニック冪商の自由性の入力。

## 方針

小数指数ごとの座標同型が通常多項式環上線形であることを、単項式の積で確かめる。
整数指数の加法が小数部分を保つ公式を使う。

## 規約

p は正とする。係数環の標数・非零性は不要。
標準評価射の toAlgebra に関する自由性を述べる。

## 使われ方

モニック冪商へ基底変更して、元の係数環上の自由基底を構成する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp
local notation "G" => powerRootExponentMonoid p hp
local notation "F" => PowerRootFraction p hp
local notation "E" => powerRootPolynomialCoordinates R p hp

/-- 概要：小数指数ごとの座標は通常多項式環のスカラー作用を保つ。
方針：多項式と有限台係数を単項式へ分解し、指数の整数平行移動を計算する。
規約：作用は Y₀ への標準多項式評価射による。
使われ方：BS Rem 7.15（著者版 p.62）の通常多項式環上の自由基底。 -/
theorem powerRootPolynomialCoordinates_smul :
    letI := powerRootPolynomialBaseAlgebra R p hp
    ∀ (f : R[X]) (x : P), E (f • x) = f • E x := by
  let := powerRootPolynomialBaseAlgebra R p hp
  intro f x
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [add_smul, map_add, hf, hg, add_smul]
  | monomial n a =>
      let e0 : P ≃ₗ[R] (G →₀ R) := AddMonoidAlgebra.coeffLinearEquiv R
      obtain ⟨v, rfl⟩ := e0.symm.surjective x
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw =>
          change E ((Polynomial.monomial n a) • AddMonoidAlgebra.ofCoeff v) =
            (Polynomial.monomial n a) • E (AddMonoidAlgebra.ofCoeff v) at hv
          change E ((Polynomial.monomial n a) • AddMonoidAlgebra.ofCoeff w) =
            (Polynomial.monomial n a) • E (AddMonoidAlgebra.ofCoeff w) at hw
          change E ((Polynomial.monomial n a) •
              (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)) =
            (Polynomial.monomial n a) • E
              (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)
          rw [smul_add, map_add, hv, hw, map_add, smul_add]
      | single q b =>
          change E ((powerRootPolynomialBaseMap R p hp (Polynomial.monomial n a)) *
              AddMonoidAlgebra.single q b) =
            (Polynomial.monomial n a) • E (AddMonoidAlgebra.single q b)
          rw [powerRootPolynomialBaseMap_monomial, AddMonoidAlgebra.single_mul_single,
            powerRootPolynomialCoordinates_single, powerRootPolynomialCoordinates_single,
            powerRootExponentSplit_nat_add]
          simp [Finsupp.smul_single, smul_eq_mul, Polynomial.monomial_mul_monomial]

/-- 概要：小数指数座標の同型は、通常多項式環上の線形同型でもある。
方針：元の加法同型に検証済みのスカラー作用の保存を付ける。
規約：標準評価射の toAlgebra を局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）のモニック商への基底変更。 -/
def powerRootPolynomialCoordinatesPolynomialLinearEquiv :
    letI := powerRootPolynomialBaseAlgebra R p hp
    P ≃ₗ[R[X]] (F →₀ R[X]) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact { (E).toAddEquiv with map_smul' := powerRootPolynomialCoordinates_smul R p hp }

/-- 概要：1 未満の指数の単項式が通常多項式環上の基底を与える。
方針：通常多項式環上の座標同型を基底の repr とする。
規約：係数環の非零性や標数を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の P/(fᵖ) の自由性。 -/
def powerRootPolynomialFractionBasis :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Basis F R[X] P := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact Module.Basis.ofRepr (powerRootPolynomialCoordinatesPolynomialLinearEquiv R p hp)

/-- 概要：小数指数基底の値はその指数の係数 1 の単項式そのもの。
方針：座標同型で両辺を比較し、小数指数の床が零であることを使う。
規約：基底の存在だけでなく具体的な値を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の明示的自由基底。 -/
theorem powerRootPolynomialFractionBasis_apply (a : F) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    powerRootPolynomialFractionBasis R p hp a = AddMonoidAlgebra.single a.val 1 := by
  let := powerRootPolynomialBaseAlgebra R p hp
  have hs : powerRootExponentSplit p hp a.val = (0, a) := by
    apply Prod.ext
    · exact Nat.floor_eq_zero.mpr a.property
    · apply Subtype.ext
      apply Subtype.ext
      exact Int.fract_eq_self.mpr ⟨powerRootExponent_nonneg p hp a.val, a.property⟩
  apply (E).injective
  change E ((E).symm (Finsupp.single a 1)) = E (AddMonoidAlgebra.single a.val 1)
  rw [LinearEquiv.apply_symm_apply, powerRootPolynomialCoordinates_single, hs]
  simp

/-- 概要：無限 p 冪根多項式環は標準通常多項式環上自由。
方針：具体的な小数指数基底から自由性を得る。
規約：作用は通常変数を Y₀ に送る射による。
使われ方：BS Rem 7.15（著者版 p.62）のモニック冪商と係数環上の自由性。 -/
theorem powerRootPolynomial_free_over_polynomial :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Free R[X] P := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact Module.Free.of_basis (powerRootPolynomialFractionBasis R p hp)

end SerrePositivity.BhattScholze.Andre
