module

public import SerrePositivity.BhattScholze.Andre.PowerRootVarpiPrimeFrobeniusPD
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateVarpiFlat
public import SerrePositivity.BhattScholze.Andre.SemilinearTensorBaseChange

/-!
# André E1・E2：実 Hodge–Tate ϖ 剰余の係数 Frobenius 底変換

## 概要

元の実 Hodge–Tate 候補の自然な ϖ 商を R/ϖ → R/p の係数 Frobenius で
通常テンソル底変換すると、元の f の mod p 入力の主分冪表示と R/p 代数同型。
BS Rem 7.15（著者版 p.62）の Frobenius 引戻しの具体的係数比較。

## 方針

二重商・逆係数 pd 表示・係数 Frobenius の三つの比較を合成し、半線形同型を実底変換する。

## 規約

底環は R/p と明示する。原典の R/ϖ 表記との最終照合と絶対 prismatic 源の同定は別工程。

## 使われ方

元の f の正確な入力を持つ pd 包への実テンソル比較を供給する。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
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
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Iv" => Ideal.span {v}
local notation "Rv" => R ⧸ Iv
local notation "S" => H ⧸ Ideal.span {dH, xH}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

local notation "Rp" => R ⧸ Ideal.span {(p : R)}
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

/-- 概要：元の自然な ϖ 商は元の mod p 入力の pd 表示と半線形環同型。
方針：二重商・逆係数表示・Frobenius 係数表示を合成する。
規約：環同型の係数 Frobenius は次の公式で明示する。
使われ方：BS Rem 7.15（著者版 p.62）の実テンソル比較の入力。 -/
def powerRootPrismMonicVarpiFrobeniusResidueEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    Mv ≃+* Dp := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let E₁ := powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf
  let E₂ := powerRootPrismMonicVarpiResidueAlgEquiv W hW f hf
  exact E₁.toRingEquiv.trans (E₂.toRingEquiv.trans (powerRootVarpiPrimeFrobeniusPDEquiv W hW f))

/-- 概要：実剰余比較は自然な R/ϖ 係数に指定 Frobenius を作用させる。
方針：二つの代数同型の可換性と pd 係数同型の公式を使う。
規約：元の ϖ 商の自然な係数作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）のテンソル普遍射の半線形性。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_coeff (hf : f.Monic) (r : Rv) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f hf (algebraMap Rv Mv r) =
      algebraMap Rp Dp (evp r) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let E₁ := powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf
  let E₂ := powerRootPrismMonicVarpiResidueAlgEquiv W hW f hf
  change powerRootVarpiPrimeFrobeniusPDEquiv W hW f (E₂ (E₁ (algebraMap Rv Mv r))) = _
  rw [E₁.commutes, E₂.commutes, powerRootVarpiPrimeFrobeniusPDEquiv_coeff]

/-- 概要：自然な実 ϖ 商の Frobenius テンソル底変換は元の mod p 入力の pd 表示。
方針：半線形環同型を通常テンソル底変換の代数同型へ直す。
規約：モニック性以外の次数・p 正則性仮定を加えない。
使われ方：BS Rem 7.15（著者版 p.62）の実引戻しと正確な入力の接続。 -/
def powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    Rp ⊗[Rv] Mv ≃ₐ[Rp] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  exact tensorBaseChangeAlgEquivOfSemilinearRingEquiv evp
    (powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f hf)
    (powerRootPrismMonicVarpiFrobeniusResidueEquiv_coeff W hW f hf)

/-- 概要：実引戻し比較は単純テンソルを標準係数と実剰余像の積へ送る。
方針：半線形テンソル同型の単純テンソル公式を適用する。
規約：全ての実 ϖ 剰余元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の根変数と元の係数の追跡。 -/
theorem powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_tmul (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    ∀ (r : Rp) (m : Mv),
      powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv W hW f hf (r ⊗ₜ[Rv] m) =
        algebraMap Rp Dp r * powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f hf m := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  dsimp only
  intro r m
  exact tensorBaseChangeAlgEquivOfSemilinearRingEquiv_tmul _ _ _ r m

end SerrePositivity.BhattScholze.Andre
