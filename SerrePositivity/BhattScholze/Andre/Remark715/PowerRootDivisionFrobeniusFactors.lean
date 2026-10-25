module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootFrobeniusFactors
public import SerrePositivity.BhattScholze.Andre.Variants.DeltaDivisionCoefficientAutComposition

/-!
# André E1・E2：raw 除算包上での Frobenius 成分の合成

## 概要

無限根入力の raw 除算包に、係数 Frobenius と指数 Frobenius を別々に作用させる。
両比較射の合成は、合成自己同型が誘導する raw 射と一致する。
BS Rem 7.15（著者版 p.62）の φ_A 係数変更と全体 Frobenius の関係。

## 方針

両成分の δ 互換性を raw 係数自己同型の一般構成へ供給し、合成の一般補題を適用する。

## 規約

未完備の環を扱う。係数成分は根変数を固定し、指数成分は係数を固定する。

## 使われ方

Frobenius による剰余比較と原典の係数引戻しを、変数の再配置を記録して結ぶ。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
variable (D : DeltaStructure p A) (hD : D.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hD.p_mul_injective D
local notation "C" => powerRootCoefficientFrobeniusEquiv p D hD
local notation "V" => powerRootVariableFrobeniusEquiv (A := A) p
local notation "hC" => powerRootCoefficientFrobeniusEquiv_isDeltaHom p D hD
local notation "hV" => powerRootVariableFrobeniusEquiv_isDeltaHom p D hD
variable {σ : Type v}
variable (d : PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime)))
variable (a : σ → PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime)))

/-- 概要：係数 Frobenius のみを適用する raw 除算包の同型。
方針：係数成分の δ 自己同型を一般の raw 比較に渡す。
規約：入力族と分母の係数だけを送る。
使われ方：BS Rem 7.15（著者版 p.62）の φ_A 係数変更の代数的部分。 -/
def powerRootCoefficientDivisionFrobeniusEquiv :
    DeltaAdjoinDivision E d a ≃+* DeltaAdjoinDivision E (C d) (fun s => C (a s)) :=
  deltaDivisionCoefficientAutEquiv E C hC d a

/-- 概要：指数 p 倍のみを適用する raw 除算包の同型。
方針：指数成分の δ 自己同型を一般の raw 比較に渡す。
規約：入力の係数環 A を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の原典の係数引戻しと変数作用の分離。 -/
def powerRootVariableDivisionFrobeniusEquiv :
    DeltaAdjoinDivision E d a ≃+* DeltaAdjoinDivision E (V d) (fun s => V (a s)) :=
  deltaDivisionCoefficientAutEquiv E V hV d a

/-- 概要：係数成分の後に指数成分を適用した raw 射は合成自己同型の raw 射。
方針：一般の係数自己同型比較の合成則を実無限根入力へ適用する。
規約：全体 Frobenius が二成分の合成であることは前ファイルの計算公式で固定済み。
使われ方：BS Rem 7.15（著者版 p.62）の raw 包における二つの Frobenius の比較。 -/
theorem powerRootDivisionFrobeniusFactors_comp :
    (powerRootVariableDivisionFrobeniusEquiv p D hD (C d) (fun s => C (a s))).toRingHom.comp
      (powerRootCoefficientDivisionFrobeniusEquiv p D hD d a).toRingHom =
    (deltaDivisionCoefficientAutEquiv E ((C).trans V) ((hV).comp hC) d a).toRingHom :=
  deltaDivisionCoefficientAutMap_trans E C V hC hV d a

end SerrePositivity.BhattScholze.Andre
