module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateCompletelyFlat
public import SerrePositivity.BhattScholze.Andre.CompletelyFaithfullyFlatPrincipalPower

/-!
# André E1・E2：自然な Hodge–Tate 候補の p 完全忠実平坦性

## 概要

p 正則な prism 商を持つ完全 prism 上の正次数モニック無限根入力について、
元の実完備化の分母商は自然な基底射で p 完全忠実平坦。
BS Rem 7.15（著者版 p.62）の p ねじれなしの場合の具体的候補。

## 方針

検証済みの ϖ 完全忠実平坦性を正冪へ移す一般補題に渡し、(ϖ^p)=(p) で書き換える。

## 規約

元の raw 包・実完備化・分母商と自然な基底射を保持する。
原典の prismatic 源および Frobenius 引戻し pd 包との同定は別工程。

## 使われ方

原典の prismatic 源の比較と最終完全 δ 化への具体的平坦性入力。
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
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
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


include hpR hf hdeg in
/-- 概要：正次数モニック入力の自然な Hodge–Tate 候補は p 完全忠実平坦。
方針：ϖ 完全忠実平坦性の正冪保存と主イデアル等式 (ϖ^p)=(p) を使う。
規約：prism 商の p 正則性と正次数を明示し、候補を別の商へ取り替えない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的候補の完全忠実平坦性。 -/
theorem powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  have h := completelyFaithfullyFlat_principal_power_algebra v T
    (powerRootPrismMonicHodgeTate_varpi_completelyFaithfullyFlat W hW hpR f hf hdeg) p hp
  rwa [perfectPrismVarpi_span_pow W hW] at h

end SerrePositivity.BhattScholze.Andre
