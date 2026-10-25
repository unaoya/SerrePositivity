module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionRegular
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicVarpiFlat

/-!
# André E1・E2：無限根モニック Hodge–Tate 候補の基底射と ϖ 商

## 概要

実完備化の分母商 T に prism 商 R から自然な基底射を与え、T の ϖ 商を既存の二元商と同定する。
BS Rem 7.15（著者版 p.62）の通常剰余の忠実平坦性への接続。

## 方針

係数射を分母商へ降ろし、標準二重主商同型で生成元と ϖ 持上げの二元商へ移す。

## 規約

元の実完備化と標準係数射を保持する。モニック性はこの比較には不要。

## 使われ方

既存の R/ϖ 上の pd 計算を、自然な R 代数 T の剰余へ移す。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
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
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}

/-- 概要：prism 商から実完備化の分母商への自然な基底射。
方針：係数射の生成元像が分母商で零となることを使って降ろす。
規約：モニック性・prism 商の p 正則性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の Hodge–Tate 候補の係数作用。 -/
def powerRootPrismMonicHodgeTateBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    R →+* T := by
  let := pdCompletionCommRing L p (jL dP)
  apply Ideal.Quotient.lift W.ideal ((qH).comp ((uL).comp ((jL).comp (algebraMap A P))))
  change Ideal.span {W.generator} ≤ RingHom.ker _
  apply Ideal.span_le.mpr
  intro r hr
  rcases Set.mem_singleton_iff.mp hr with rfl
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self dH)

/-- 概要：基底射は A の代表元をその標準完備化係数像へ送る。
方針：商への降下の計算規則を使う。
規約：全ての係数元 r を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の自然な作用の照合。 -/
theorem powerRootPrismMonicHodgeTateBaseMap_mk (r : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateBaseMap W hW f (Ideal.Quotient.mk W.ideal r) =
      qH (uL (jL (algebraMap A P r))) := rfl

/-- 概要：基底の ϖ は選んだ持上げの標準像へ送られる。
方針：係数代表元公式を適用する。
規約：ϖ は生成元の逆 Frobenius 像から選ぶ。
使われ方：BS Rem 7.15（著者版 p.62）の T/ϖ の実商比較。 -/
theorem powerRootPrismMonicHodgeTateBaseMap_varpi :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateBaseMap W hW f (perfectPrismVarpi W hW) = qH xH := rfl

/-- 概要：自然な Hodge–Tate 候補の ϖ 商は実完備化の指定二元商と環同型。
方針：ϖ の標準像公式と二重主商同型を使う。
規約：係数射を変えず、モニック性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の既存 pd 剰余計算の移送。 -/
def powerRootPrismMonicHodgeTateVarpiEquiv :
    let := pdCompletionCommRing L p (jL dP)
    (T ⧸ Ideal.span {powerRootPrismMonicHodgeTateBaseMap W hW f (perfectPrismVarpi W hW)}) ≃+*
      S := by
  let := pdCompletionCommRing L p (jL dP)
  exact principalDoubleQuotEquiv dH xH

/-- 概要：ϖ 商比較は実完備化の代表元を保つ。
方針：二重主商同型の代表元公式を使う。
規約：実 H⁰ の全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数線形性の確認。 -/
theorem powerRootPrismMonicHodgeTateVarpiEquiv_mk (t : H) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateVarpiEquiv W hW f
      (Ideal.Quotient.mk _ (qH t)) = Ideal.Quotient.mk _ t := by
  let := pdCompletionCommRing L p (jL dP)
  exact principalDoubleQuotEquiv_mk dH xH t

end SerrePositivity.BhattScholze.Andre
