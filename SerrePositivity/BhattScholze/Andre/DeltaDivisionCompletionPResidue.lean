module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionFrobeniusCompletionToRaw
public import SerrePositivity.BhattScholze.Andre.DeltaDivisionFrobeniusPResidueEquiv

/-!
# André E1・E2：実完備化の剰余を raw p 除算剰余へ接続

## 概要

完全 δ 環の distinguished d に対し、A{a/d} の実完備化後の
(d,φ⁻¹(d)) 商を A{φ(a)/p}/(p,d) と環同型にする。
BS Rem 7.15（著者版 p.62）の具体的 pd 包比較への接続。

## 方針

実完備化から Frobenius 側 raw 剰余への同型に、Witt 単元による分母変換を合成する。

## 規約

実 H⁰ とその標準単位を維持する。原典とは異なる Witt 座標による証明である。

## 使われ方

既存の raw p 除算包と pd 表示との比較へ、実完備化の剰余を渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) (a : σ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "H" => PDCompletionH0 L p (jL d)
local notation "uL" => pdCompletionUnit L p (jL d)
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "b" => fun s => D.frobeniusLift (a s)
local notation "Qp" => DeltaDivisionPairResidue D (p : A) b d

/-- 概要：実完備化後の二元剰余は Frobenius 分子の raw p 除算剰余と環同型。
方針：実完備化から raw への比較に、Witt 単元による分母変換を合成する。
規約：完全 δ 環、distinguished d、源の p 正則性と ghost 単射性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化から具体的 pd 包への接続。 -/
def deltaDivisionCompletionPResidueEquiv :
    letI := pdCompletionCommRing L p (jL d)
    (H ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+* Qp := by
  let := pdCompletionCommRing L p (jL d)
  exact (deltaDivisionFrobeniusCompletionToRawEquiv D hD d a hd).trans
    (deltaDivisionFrobeniusPResidueEquiv D hpA hgA hgL d hd b)

/-- 概要：実完備化から raw p 剰余への同型は係数 r を φ(r) の剰余へ送る。
方針：Frobenius 比較の係数公式と分母変換の係数保存を使う。
規約：元の標準完備化単位を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 引戻しの係数作用を追う。 -/
theorem deltaDivisionCompletionPResidueEquiv_coeff (r : A) :
    letI := pdCompletionCommRing L p (jL d)
    deltaDivisionCompletionPResidueEquiv D hpA hgA hgL hD d hd a
        (Ideal.Quotient.mk _ (uL (jL r))) =
      deltaDivisionPairResidueBase D (p : A) b d (D.frobeniusLift r) := by
  let := pdCompletionCommRing L p (jL d)
  rw [deltaDivisionCompletionPResidueEquiv, RingEquiv.trans_apply,
    deltaDivisionFrobeniusCompletionToRawEquiv_coeff]
  exact deltaDivisionFrobeniusPResidueEquiv_base D hpA hgA hgL d hd b (D.frobeniusLift r)

end SerrePositivity.BhattScholze.Andre
