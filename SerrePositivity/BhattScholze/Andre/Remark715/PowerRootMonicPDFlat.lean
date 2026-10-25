module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicQuotient
public import SerrePositivity.BhattScholze.Andre.Remark715.MonicPDFlat

/-!
# André E1・E2：無限 p 冪根多項式環上のモニック分冪表示環の自由性

## 概要

標数 p の係数環上の無限 p 冪根多項式環 P 内で、モニック f の像の分冪表示環は
元の係数環上自由であり、f が正次数なら忠実平坦。
BS Rem 7.15（著者版 p.62）の通常代数の自由性計算。

## 方針

同じ実 fᵖ 商の自由性・忠実平坦性と、その商上の分冪表示環の自由性を合成する。
標準多項式係数射で拡張したイデアルを、f の像の p 乗の主イデアルへ同定する。

## 規約

対象は既存の PrincipalDPPresentation である。
実 prismatic envelope の Frobenius 引戻しや実 pd 包との同定をこのファイルだけでは主張しない。

## 使われ方

原典の具体的 pd 計算と既存候補の比較を補完する際に、通常係数環の自由性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：無限 p 冪根変数内のモニック関係の分冪表示環は元の係数環上自由。
方針：実 fᵖ 商の自由性と、その商上の分冪表示環の自由性をスカラー塔で合成する。
規約：p は素数で係数環内で零とする。自由性には f の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の pd 表示の自由性。 -/
theorem powerRootMonicDPPresentation_free (hprime : p.Prime) (hpR : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) :
    Module.Free R (PrincipalDPPresentation P (powerRootPolynomialBaseMap R p hp f)) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let y := powerRootPolynomialBaseMap R p hp f
  have hpP : (p : P) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R P) hpR
  have heI : (Ideal.span {f ^ p}).map (algebraMap R[X] P) = Ideal.span {y ^ p} := by
    rw [powerRootPolynomialQuotient_ideal, map_pow]
  have hQ : Module.Free R (P ⧸ Ideal.span {y ^ p}) := by
    have h := powerRootPolynomialPowerQuotient_free R p hp f hf
    change Module.Free R (P ⧸ (Ideal.span {f ^ p}).map (algebraMap R[X] P)) at h
    rw [heI] at h
    exact h
  let := principalDPQuotientAlgebra hprime.pos hpP y
  let := principalDPQuotient_isScalarTower_base (A := R) hprime.pos hpP y
  let := principalDPPresentation_quotient_free p hprime hpP y
  let := hQ
  exact Module.Free.trans (R := R) (S := P ⧸ Ideal.span {y ^ p})
    (M := PrincipalDPPresentation P y)

/-- 概要：正次数モニック関係の分冪表示環は元の係数環上忠実平坦。
方針：同じ実 fᵖ 商の忠実平坦性を標準係数射のスカラー塔で表示環へ移す。
規約：係数環の非零性や被約性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の原典の通常平坦性計算。 -/
theorem powerRootMonicDPPresentation_faithfullyFlat (hprime : p.Prime) (hpR : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R
      (PrincipalDPPresentation P (powerRootPolynomialBaseMap R p hp f)) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let y := powerRootPolynomialBaseMap R p hp f
  have hpP : (p : P) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R P) hpR
  have heI : (Ideal.span {f ^ p}).map (algebraMap R[X] P) = Ideal.span {y ^ p} := by
    rw [powerRootPolynomialQuotient_ideal, map_pow]
  apply principalDPPresentation_faithfullyFlat_of_quotient p hprime hpP y
  have h := powerRootPolynomialPowerQuotient_faithfullyFlat R p hp f hf hdeg
  change Module.FaithfullyFlat R (P ⧸ (Ideal.span {f ^ p}).map (algebraMap R[X] P)) at h
  rw [heI] at h
  exact h

end SerrePositivity.BhattScholze.Andre
