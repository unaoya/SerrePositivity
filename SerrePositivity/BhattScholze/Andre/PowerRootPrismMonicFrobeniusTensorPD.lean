module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicFrobeniusTensorAlgebra
public import SerrePositivity.BhattScholze.Andre.PowerRootPrimeFrobeniusPDEnvelope
public import SerrePositivity.BhattScholze.Andre.PrincipalPDSourceTransport

/-!
# André R1：自然な Frobenius テンソルの PD 入力とイデアル

## 概要

自然な Frobenius テンソルにおける標準入力環作用、比較同型、分冪イデアルを保持する。
BS Rem 7.15(1)（著者版 p.62）の元の入力と同じ台環を使う。

## 方針

係数と根変数を保つ比較同型により入力作用と指定イデアルを作る。
原典とは異なる半線形比較・通常テンソルを使う経路。

## 規約

不要になった hpR 付きの分冪構造・分冪射・分冪公式・普遍性の4宣言を削除した。
対応する `_of_unconditional` 版を集約から公開し、モニック性を保持して正次数は追加しない。

## 使われ方

無条件の分冪構造を、同じ元の実引戻しと同じ入力作用に関して適用する。
-/

@[expose] public noncomputable section
universe u w
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

local notation "Ft" => Rp ⊗[Rv] Mv
local notation "Et" => powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv W hW f

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf

/-- 概要：実テンソルの分冪イデアルは標準正次数イデアルの逆像。
方針：自然な入力環上の代数同型の逆で像イデアルを取る。
規約：元の実テンソル環を維持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の台イデアル。 -/
def powerRootPrismMonicFrobeniusTensorPDIdeal :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    Ideal Ft := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  exact principalPDSourceIdeal zp Ein

/-- 概要：自然な実テンソルの分冪イデアルは元の入力の像を含む。
方針：係数を保つ同型の源への入力所属の一般公式を使う。
規約：モニック性のみを仮定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪包の入力条件。 -/
theorem powerRootPrismMonicFrobeniusTensorPDIdeal_input_mem :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft zp ∈ powerRootPrismMonicFrobeniusTensorPDIdeal W hW f hf := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  exact principalPDSourceIdeal_base_mem zp Ein

end SerrePositivity.BhattScholze.Andre
