module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionCompletionPResidue
public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaPDivisionIdealPDComparison

/-!
# André E1・E2：実完備化の二元剰余と標準主 pd 表示

## 概要

完全 δ 環上の一元 raw 包 A{y/d} の実完備化後の (d,φ⁻¹(d)) 商は、
A/(p,d) 上の y の標準主分冪表示と環同型。
BS Rem 7.15（著者版 p.62）の具体的な pd 台環の比較。

## 方針

実完備化剰余を raw φ(y)/p 剰余へ移し、既存の階乗計算と係数イデアル商を合成する。

## 規約

源の完全性・p 正則性・p 局所性、d の distinguished 性、y mod p の正則性を明示する。
原典とは異なる Witt 座標による証明。prismatic 源との同定は別工程。

## 使われ方

無限根多項式環上のモニック入力へ適用して原典の具体的 pd 包へ接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun r : A => (p : A) * r))
variable (D : DeltaStructure p A) (hD : D.IsPerfect)
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (hd : D.IsDistinguished d) (y : A)
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a" => fun _ : σ => y
local notation "L" => DeltaAdjoinDivision D d a
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "H" => PDCompletionH0 L p (jL d)
local notation "uL" => pdCompletionUnit L p (jL d)
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "K" => Ideal.span {(p : A), d}
local notation "R" => A ⧸ K
local notation "bar" => Ideal.Quotient.mk K

/-- 概要：実完備化後の一元 raw 剰余は係数二元商上の標準主分冪表示と環同型。
方針：Frobenius と Witt 分母変換による比較に raw-pd 係数商同型を合成する。
規約：仮定は源と入力の正則性・局所性・完全性であり、比較同型自体は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の剰余の具体的 pd 表示。 -/
def deltaDivisionCompletionPrincipalPDEquiv :
    letI := pdCompletionCommRing L p (jL d)
    (H ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+* PrincipalDPPresentation R (bar y) := by
  let := pdCompletionCommRing L p (jL d)
  exact (deltaDivisionCompletionPResidueEquiv D hpA hgA hgL hD d hd a).trans
    (deltaPDivisionPairPDEquiv hA hpA D y hgL v hv hy d)

/-- 概要：実完備化の pd 台環比較は係数 r を φ(r) の剰余係数へ送る。
方針：実完備化から raw への係数公式と raw-pd の係数保存を使う。
規約：実完備化単位と元の係数射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 引戻しを係数上で照合する。 -/
theorem deltaDivisionCompletionPrincipalPDEquiv_coeff (r : A) :
    letI := pdCompletionCommRing L p (jL d)
    deltaDivisionCompletionPrincipalPDEquiv hA hpA D hD hgA hgL d hd y v hv hy
        (Ideal.Quotient.mk _ (uL (jL r))) =
      algebraMap R (PrincipalDPPresentation R (bar y)) (bar (D.frobeniusLift r)) := by
  let := pdCompletionCommRing L p (jL d)
  rw [deltaDivisionCompletionPrincipalPDEquiv, RingEquiv.trans_apply,
    deltaDivisionCompletionPResidueEquiv_coeff]
  exact deltaPDivisionPairPDEquiv_coeff hA hpA D y hgL v hv hy d (D.frobeniusLift r)

end SerrePositivity.BhattScholze.Andre
