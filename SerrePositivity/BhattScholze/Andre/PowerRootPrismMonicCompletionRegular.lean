module

public import SerrePositivity.BhattScholze.Andre.PrincipalPairCompletionFirstRegular
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicRawPairRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete
public import SerrePositivity.BhattScholze.PDCompletionInterface

/-!
# André E1・E2：無限根モニック実完備化と Hodge–Tate 商の p 正則性

## 概要

p 正則な prism 商を持つ完全 prism 上の無限根モニック raw 包の実 (p,d) 完備化 H⁰ と、
その分母商には p ねじれがない。BS Rem 7.15（著者版 p.62）の p ねじれなしの場合。

## 方針

元の raw 包の p,d 正則対を実反復完備化と標準剰余比較に移す。

## 規約

元の Koszul 完備化 H⁰ と標準射を使う。prism 商の p 正則性を明示し、正次数は不要。

## 使われ方

原典の prismatic 源との同定、および Hodge–Tate 商の p 完全忠実平坦性への入力。
-/

@[expose] public noncomputable section
universe u
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
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "dL" => deltaAdjoinDivisionMap E dP a dP
local notation "H" => PDCompletionH0 Raw p dL

include hpR hf in
/-- 概要：無限根モニック raw 包の実二座標完備化 H⁰ は p 正則。
方針：raw 包の正則対へ実二座標完備化の第一元正則性を適用する。
規約：prism 商の p 正則性を仮定し、正次数を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化に新しい p ねじれがないこと。 -/
theorem powerRootPrismMonic_pdCompletion_prime_regular :
    let := pdCompletionCommRing Raw p dL
    IsSMulRegular H (p : H) := by
  have h := principalPair_pairCompletion_first_regular (p : Raw) dL
    (powerRootPrismMonicRaw_p_mul_injective W hW hpR f hf)
    (powerRootPrismMonicRaw_mod_prime_generator_regular W hW hpR f hf)
  let := pdCompletionCommRing Raw p dL
  simpa only [map_natCast] using h

include hpR hf in
/-- 概要：無限根モニック実完備化の分母商は p 正則。
方針：raw 包の正則対へ実二座標完備化の第二元商での第一元正則性を適用する。
規約：実 H⁰ の標準分母像で割る通常商を使う。
使われ方：BS Rem 7.15（著者版 p.62）の Hodge–Tate 候補の p ねじれの排除。 -/
theorem powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular :
    let := pdCompletionCommRing Raw p dL
    IsSMulRegular (H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL})
      (p : H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}) := by
  have h := principalPair_pairCompletion_mod_second_first_regular (p : Raw) dL
    (powerRootPrismMonicRaw_p_mul_injective W hW hpR f hf)
    (powerRootPrismMonicRaw_mod_prime_generator_regular W hW hpR f hf)
  let := pdCompletionCommRing Raw p dL
  change IsSMulRegular (H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL})
    (Ideal.Quotient.mk (Ideal.span {pdCompletionUnit Raw p dL dL})
      (pdCompletionUnit Raw p dL (p : Raw))) at h
  simpa only [map_natCast] using h

include hpR hf in
/-- 概要：無限根モニック実完備化の分母商は通常の意味でも p 完備。
方針：実 H⁰ の導来 p 完備性を主商へ移し、p 正則性で古典的完備性と比較する。
規約：標準分母像による元の通常商を使う。
使われ方：BS Rem 7.15（著者版 p.62）の p 完全忠実平坦性の環候補。 -/
theorem powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete :
    let := pdCompletionCommRing Raw p dL
    let T := H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}
    IsAdicComplete (Ideal.span {(p : T)}) T := by
  let := pdCompletionCommRing Raw p dL
  let T := H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}
  have hreg : IsSMulRegular T (p : T) :=
    powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular W hW hpR f hf
  apply (isRingModuleComplete_iff_isAdicComplete_natCast T p hreg).mp
  exact isModuleComplete_principal_quotient_natCast H p (pdCompletionUnit Raw p dL dL)
    (pdCompletionH0_self_complete_p Raw p dL)

end SerrePositivity.BhattScholze.Andre
