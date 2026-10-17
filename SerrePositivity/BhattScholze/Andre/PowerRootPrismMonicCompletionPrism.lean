module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateRoot
public import SerrePositivity.BhattScholze.DeltaPDCompletion

/-!
# André E1・E2：無限根モニック raw 包の実完備化 prism

## 概要

p 正則な prism 商を持つ完全 prism 上で、無限根モニック raw 包の実完備化は
標準分母像を生成元とする oriented prism となる。BS Rem 7.15（著者版 p.62）の源候補。

## 方針

既存の実完備化の δ 構造、分母の distinguished 性、検証済みの正則性と導来完備性を結ぶ。

## 規約

完全 prism であることは主張しない。原典の prismatic envelope との普遍性比較は別工程。

## 使われ方

同じ具体的候補の p 完全忠実平坦性と根を、prismatic 源の比較へ接続する。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)

include hpR hf in
/-- 概要：元の無限根モニック実完備化に標準分母像を生成元とする prism 構造を与える。
方針：distinguished 性を二つの標準 δ 射で移し、実完備化の正則性と完備性を使う。
規約：prism 商の p 正則性を明示し、正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の原典の prismatic 源との比較の入力。 -/
def powerRootPrismMonicCompletionPrism :
    let := pdCompletionCommRing L p (jL dP)
    OrientedPrism p H := by
  let := pdCompletionCommRing L p (jL dP)
  have hdL : (DL).IsDistinguished (jL dP) := by
    have h := (powerRootPrismGenerator_isDistinguished W hW).map jL
    rw [deltaAdjoinDivisionMap_isDeltaHom E dP a dP] at h
    exact h
  have hdH : (DH).IsDistinguished (uL (jL dP)) := by
    have h := hdL.map uL
    rw [pdCompletionUnit_isDeltaHom DL (jL dP) (jL dP)] at h
    exact h
  exact OrientedPrism.ofDistinguished DH (uL (jL dP)) hdH
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW hpR f hf)
    (pdCompletionH0_self_complete_p L p (jL dP))
    (pdCompletionH0_self_complete_d L p (jL dP))

/-- 概要：元の係数 prism の台環から実完備化への標準射。
方針：無限根係数射、raw 射、実完備化単位を合成する。
規約：環射自体にモニック性や p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の基底 prism 上の比較。 -/
def powerRootPrismMonicCompletionBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    A →+* H := by
  let := pdCompletionCommRing L p (jL dP)
  exact (uL).comp ((jL).comp (algebraMap A P))

/-- 概要：標準係数射は元の δ 構造と実完備化の δ 構造を保つ。
方針：三つの既存の標準 δ 射を合成する。
規約：元の指定 δ 構造を使う。
使われ方：BS Rem 7.15（著者版 p.62）の prism 射の δ 条件。 -/
theorem powerRootPrismMonicCompletionBaseMap_isDeltaHom :
    let := pdCompletionCommRing L p (jL dP)
    W.deltaStructure.IsDeltaHom DH (powerRootPrismMonicCompletionBaseMap W hW f) := by
  let := pdCompletionCommRing L p (jL dP)
  exact (pdCompletionUnit_isDeltaHom DL (jL dP)).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E dP a).comp
      (powerRootPolynomialDelta_coeff_isDeltaHom p hW.p_mul_injective W.deltaStructure))

include hpR hf in
/-- 概要：標準係数射は指定 prism 生成元を実完備化 prism の指定生成元へ送る。
方針：双方の標準射と生成元の定義を展開する。
規約：生成元は変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の基底 prism 上の比較。 -/
theorem powerRootPrismMonicCompletionBaseMap_generator :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicCompletionBaseMap W hW f W.generator =
      (powerRootPrismMonicCompletionPrism W hW hpR f hf).generator := rfl

end SerrePositivity.BhattScholze.Andre
