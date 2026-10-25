module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionPD
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootFrobeniusPairVarpiInput
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiNativePDFlat

/-!
# André E1・E2：実完備化剰余と逆 Frobenius 係数入力の ϖ pd 表示

## 概要

無限根モニック raw 包の実完備化の二元剰余を R/ϖ 上の主 pd 表示と比較する。
標準変数を固定した入力は逆 Frobenius で係数変更した多項式である。
BS Rem 7.15（著者版 p.62）への比較で係数作用を明示する。

## 方針

(p,d) 係数の主分冪表示を逆係数 Frobenius で移し、実完備化剰余の同型に合成する。

## 規約

元の f の pd 包との同定は主張しない。prismatic 源の同定も別工程。
原典とは異なる具体的な Witt 座標と係数変更を使う。

## 使われ方

ϖ 剰余の自然な係数作用と通常忠実平坦性を検証するための比較。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "K" => Ideal.span {(p : P), dP}
local notation "Q" => P ⧸ K
local notation "bar" => Ideal.Quotient.mk K
local notation "y" => powerRootMonicPDInput p f
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr
  (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "C" => powerRootFrobeniusPairVarpiInputEquiv W hW

/-- 概要：二元係数商上の主分冪表示は逆 Frobenius 係数入力の ϖ 表示と環同型。
方針：入力を保つ係数環同型を主分冪表示へ持ち上げる。
規約：入力 f' の係数変更を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化比較へ合成する pd 台環同型。 -/
def powerRootPrismInverseVarpiPDEquiv : PrincipalDPPresentation Q (bar y) ≃+* Dv :=
  principalDPRingEquivOfEq C (bar y) zv (powerRootFrobeniusPairVarpiInputEquiv_input W hW f)

/-- 概要：ϖ 表示への主分冪同型は全標準生成元の次数を保つ。
方針：主分冪係数同型の生成元公式を使う。
規約：全次数 n を含める。
使われ方：BS Rem 7.15（著者版 p.62）の実分冪構造の比較への入力。 -/
theorem powerRootPrismInverseVarpiPDEquiv_generator (n : ℕ) :
    powerRootPrismInverseVarpiPDEquiv W hW f (principalDPGenerator (bar y) n) =
      principalDPGenerator zv n :=
  principalDPRingEquivOfEq_generator _ _ _ _ n

/-- 概要：主分冪同型は全入力係数を明示した無限根係数同型で送る。
方針：主分冪係数同型の一般公式を使う。
規約：係数は Q の全ての元。
使われ方：BS Rem 7.15（著者版 p.62）の完備化係数作用の合成。 -/
theorem powerRootPrismInverseVarpiPDEquiv_coeff (r : Q) :
    powerRootPrismInverseVarpiPDEquiv W hW f (algebraMap Q _ r) = algebraMap Nv Dv (C r) :=
  principalDPRingEquivOfEq_coeff _ _ _ _ r

/-- 概要：実完備化の二元剰余は逆 Frobenius 係数入力の R/ϖ 主分冪表示と環同型。
方針：実完備化の二元商比較と ϖ 係数への主分冪同型を合成する。
規約：完全 prism とモニック性のみを仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の ϖ 剰余の通常平坦性への接続。 -/
def powerRootPrismMonicVarpiCompletionPDEquiv (hf : f.Monic) :
    letI := pdCompletionCommRing L p (jL dP)
    (H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}) ≃+* Dv := by
  let := pdCompletionCommRing L p (jL dP)
  exact (powerRootPrismMonicCompletionPDEquiv W hW f hf).trans
    (powerRootPrismInverseVarpiPDEquiv W hW f)

/-- 概要：実完備化比較は全無限根係数に Frobenius と明示係数比較を順に適用する。
方針：二つの環同型の係数公式を合成する。
規約：元の実完備化単位を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の変数を含む係数作用の照合。 -/
theorem powerRootPrismMonicVarpiCompletionPDEquiv_coeff (hf : f.Monic) (r : P) :
    letI := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf
        (Ideal.Quotient.mk _ (uL (jL r))) =
      algebraMap Nv Dv (C (bar ((E).frobeniusLift r))) := by
  let := pdCompletionCommRing L p (jL dP)
  rw [powerRootPrismMonicVarpiCompletionPDEquiv, RingEquiv.trans_apply,
    powerRootPrismMonicCompletionPDEquiv_coeff, powerRootPrismInverseVarpiPDEquiv_coeff]

/-- 概要：実完備化比較は元の A の係数を自然な R/ϖ 係数として保つ。
方針：Frobenius と逆係数 Frobenius の相殺と係数作用の塔を使う。
規約：逆 Frobenius 係数多項式を使った同型についての公式。
使われ方：BS Rem 7.15（著者版 p.62）の自然な ϖ 係数作用の確認。 -/
theorem powerRootPrismMonicVarpiCompletionPDEquiv_base_coeff (hf : f.Monic) (r : A) :
    letI := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf
        (Ideal.Quotient.mk _ (uL (jL (algebraMap A P r)))) = algebraMap Rv Dv (barr r) := by
  let := pdCompletionCommRing L p (jL dP)
  rw [powerRootPrismMonicVarpiCompletionPDEquiv_coeff, powerRootPolynomialDelta_frobenius,
    powerRootPolynomialFrobenius_coeff, powerRootFrobeniusPairVarpiInputEquiv_coeff]
  rw [show (W.deltaStructure.frobeniusEquiv hW).symm (W.deltaStructure.frobeniusLift r) = r from
    (W.deltaStructure.frobeniusEquiv hW).symm_apply_apply r]
  exact (IsScalarTower.algebraMap_apply Rv Nv Dv (barr r)).symm

end SerrePositivity.BhattScholze.Andre
