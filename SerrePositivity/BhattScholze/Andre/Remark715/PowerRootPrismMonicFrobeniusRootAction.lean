module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicFrobeniusBaseChange

/-!
# André E1・E2：実 Frobenius 底変換の自然な無限根作用

## 概要

実 ϖ 剰余の Frobenius テンソル比較は、元の第 n+1 根変数を第 n 根変数に送る。
BS Rem 7.15（著者版 p.62）の pd 包の自然な入力環作用を確認する。

## 方針

実完備化比較の全係数公式を根変数に適用し、テンソル同型で戻した作用を係数と根変数で検証する。

## 規約

元の実完備化と標準根変数を保持する。次数・prism 商の p 正則性は不要。

## 使われ方

実テンソル側を元の mod p 入力の pd 包として扱うための自然な作用の照合。
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

local notation "qT" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "qvT" => Ideal.Quotient.mk (Ideal.map φ Iv)
local notation "qS" => Ideal.Quotient.mk (Ideal.span {dH, xH})
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f
local notation "Et" => powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv W hW f

/-- 概要：元の無限根環から自然な実 ϖ 剰余への標準係数射。
方針：raw 射・実完備化単位・二段の通常商射を合成する。
規約：入力のモニック性は環射の定義自体に不要。
使われ方：BS Rem 7.15（著者版 p.62）の根変数の標準像。 -/
def powerRootPrismMonicVarpiInputMap :
    let := pdCompletionCommRing L p (jL dP)
    P →+* Mv := by
  let := pdCompletionCommRing L p (jL dP)
  exact (qvT).comp ((qT).comp ((uL).comp jL))

/-- 概要：半線形実剰余比較は元の第 n 根変数を比較先の第 n 根変数の p 乗へ送る。
方針：実完備化比較の全係数公式と係数・変数 Frobenius の公式を合成する。
規約：全ての段 n を含み、根を選び直さない。
使われ方：BS Rem 7.15（著者版 p.62）の自然な無限根環作用の確認。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    U hf (powerRootPrismMonicVarpiInputMap W hW f (powerRootPolynomialVariable A p hp n)) =
      algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) ^ p := by
  let := pdCompletionCommRing L p (jL dP)
  let r := powerRootPolynomialVariable A p hp n
  change powerRootVarpiPrimeFrobeniusPDEquiv W hW f
    (powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf
      (powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f
        (qvT (qT (uL (jL r)))))) = _
  rw [powerRootPrismMonicHodgeTateVarpiMapQuotEquiv_mk,
    powerRootPrismMonicVarpiCompletionPDEquiv_coeff,
    powerRootPolynomialDelta_frobenius, powerRootPolynomialFrobenius_variable]
  simp only [map_pow, powerRootFrobeniusPairVarpiInputEquiv_variable,
    powerRootVarpiPrimeFrobeniusPDEquiv, principalDPRingEquivOfEq_coeff,
    powerRootVarpiPrimeFrobeniusEquiv_variable]

/-- 概要：半線形比較は元の第 n+1 根変数を比較先の第 n 根変数へ送る。
方針：p 乗像の公式と無限根変数の隣接関係を使う。
規約：全ての段 n を含む。
使われ方：BS Rem 7.15（著者版 p.62）の底変換後の入力環の根変数。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable_succ
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    U hf (powerRootPrismMonicVarpiInputMap W hW f
      (powerRootPolynomialVariable A p hp (n + 1))) =
      algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) := by
  let := pdCompletionCommRing L p (jL dP)
  rw [powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable,
    ← map_pow, powerRootPolynomialVariable_pow]

/-- 概要：実底変換比較は 1 と元の第 n+1 根変数のテンソルを第 n 根変数へ送る。
方針：単純テンソル公式と半線形比較の隣接段公式を使う。
規約：自然な実 ϖ 商の元をそのままテンソルに入れる。
使われ方：BS Rem 7.15（著者版 p.62）の実引戻しの自然な入力環作用。 -/
theorem powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (powerRootPolynomialVariable A p hp (n + 1))
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    Et hf ((1 : Rp) ⊗ₜ[Rv] m) =
      algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (powerRootPolynomialVariable A p hp (n + 1))
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  calc
    Et hf ((1 : Rp) ⊗ₜ[Rv] m) = algebraMap Rp Dp 1 * U hf m :=
      powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_tmul W hW f hf 1 m
    _ = U hf m :=
      (congrArg (fun z : Dp => z * U hf m) (map_one (algebraMap Rp Dp))).trans
        (one_mul (U hf m))
    _ = algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) :=
      powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable_succ W hW f hf n

end SerrePositivity.BhattScholze.Andre
