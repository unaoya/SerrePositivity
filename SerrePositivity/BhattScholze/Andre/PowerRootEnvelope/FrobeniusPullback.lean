module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPrism
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary
public import SerrePositivity.BhattScholze.Andre.Variants.RootedExtension

/-!
# Frobenius 底変換と引戻しの pd 構造（BS 著者版 Remark 7.15）

## 概要
Hodge–Tate ϖ 剰余の係数 Frobenius 底変換と無限根作用、Frobenius テンソル上の代数作用と PD 入力、A 全体の Frobenius 引戻しの pd 表示と普遍性。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Unconditional/FrobeniusPD`、`Variants/MonicRootedExtension`。
-/

universe u w

/-! ## 実 Hodge–Tate ϖ 剰余の係数 Frobenius 底変換

## 概要

元の実 Hodge–Tate 候補の自然な ϖ 商を R/ϖ → R/p の係数 Frobenius で
通常テンソル底変換すると、元の f の mod p 入力の主分冪表示と R/p 代数同型。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しの具体的係数比較。

## 方針

二重商・逆係数 pd 表示・係数 Frobenius の三つの比較を合成し、半線形同型を実底変換する。

## 規約

底環は R/p と明示する。原典の R/ϖ 表記との最終照合と絶対 prismatic 源の同定は別工程。

## 使われ方

元の f の正確な入力を持つ pd 包への実テンソル比較を供給する。
-/

@[expose] public noncomputable section PowerRootPrismMonicFrobeniusBaseChange

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

/-- 概要：元の自然な ϖ 商は元の mod p 入力の pd 表示と半線形環同型。
方針：二重商・逆係数表示・Frobenius 係数表示を合成する。
規約：環同型の係数 Frobenius は次の公式で明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実テンソル比較の入力。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のテンソル普遍射の半線形性。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実引戻しと正確な入力の接続。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根変数と元の係数の追跡。 -/
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

end PowerRootPrismMonicFrobeniusBaseChange

/-! ## 実 Frobenius 底変換の自然な無限根作用

## 概要

実 ϖ 剰余の Frobenius テンソル比較は、元の第 n+1 根変数を第 n 根変数に送る。
BS 著者版 Remark 7.15（著者版 p.62）の pd 包の自然な入力環作用を確認する。

## 方針

実完備化比較の全係数公式を根変数に適用し、テンソル同型で戻した作用を係数と根変数で検証する。

## 規約

元の実完備化と標準根変数を保持する。次数・prism 商の p 正則性は不要。

## 使われ方

実テンソル側を元の mod p 入力の pd 包として扱うための自然な作用の照合。
-/

@[expose] public noncomputable section PowerRootPrismMonicFrobeniusRootAction

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根変数の標準像。 -/
def powerRootPrismMonicVarpiInputMap :
    let := pdCompletionCommRing L p (jL dP)
    P →+* Mv := by
  let := pdCompletionCommRing L p (jL dP)
  exact (qvT).comp ((qT).comp ((uL).comp jL))

/-- 概要：半線形実剰余比較は元の第 n 根変数を比較先の第 n 根変数の p 乗へ送る。
方針：実完備化比較の全係数公式と係数・変数 Frobenius の公式を合成する。
規約：全ての段 n を含み、根を選び直さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な無限根環作用の確認。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    U hf (powerRootPrismMonicVarpiInputMap W hW f (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n)) =
      algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) ^ p := by
  let := pdCompletionCommRing L p (jL dP)
  let r := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp n
  change powerRootVarpiPrimeFrobeniusPDEquiv W hW f
    (powerRootPrismMonicVarpiCompletionPDEquiv W hW f hf
      (powerRootPrismMonicHodgeTateVarpiMapQuotEquiv W hW f
        (qvT (qT (uL (jL r)))))) = _
  rw [powerRootPrismMonicHodgeTateVarpiMapQuotEquiv_mk,
    powerRootPrismMonicVarpiCompletionPDEquiv_coeff,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta_frobenius, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialFrobenius_variable]
  simp only [map_pow, powerRootFrobeniusPairVarpiInputEquiv_variable,
    powerRootVarpiPrimeFrobeniusPDEquiv, principalDPRingEquivOfEq_coeff,
    powerRootVarpiPrimeFrobeniusEquiv_variable]

/-- 概要：半線形比較は元の第 n+1 根変数を比較先の第 n 根変数へ送る。
方針：p 乗像の公式と無限根変数の隣接関係を使う。
規約：全ての段 n を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の底変換後の入力環の根変数。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable_succ
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    U hf (powerRootPrismMonicVarpiInputMap W hW f
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))) =
      algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) := by
  let := pdCompletionCommRing L p (jL dP)
  rw [powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable,
    ← map_pow, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable_pow]

/-- 概要：実底変換比較は 1 と元の第 n+1 根変数のテンソルを第 n 根変数へ送る。
方針：単純テンソル公式と半線形比較の隣接段公式を使う。
規約：自然な実 ϖ 商の元をそのままテンソルに入れる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実引戻しの自然な入力環作用。 -/
theorem powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    Et hf ((1 : Rp) ⊗ₜ[Rv] m) =
      algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  calc
    Et hf ((1 : Rp) ⊗ₜ[Rv] m) = algebraMap Rp Dp 1 * U hf m :=
      powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_tmul W hW f hf 1 m
    _ = U hf m :=
      (congrArg (fun z : Dp => z * U hf m) (map_one (algebraMap Rp Dp))).trans
        (one_mul (U hf m))
    _ = algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) :=
      powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable_succ W hW f hf n

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicFrobeniusRootAction

/-! ## 実 Frobenius テンソル上の無限根環の自然な代数作用

## 概要

実テンソルの無限根環作用は、元の次段の根変数の像と自然な係数作用で記述できる。
BS 著者版 Remark 7.15（著者版 p.62）の pd 包の入力環との比較。

## 方針

検証済みのテンソル同型で作用を戻し、全ての係数と全ての根変数上で自然な像を証明する。

## 規約

作用を暗黙の移送として残さず、係数・根変数の像を公開する。モニック性のみを仮定する。

## 使われ方

同じ実テンソルを無限根環上の実 pd 包として扱う。
-/

@[expose] public noncomputable section PowerRootPrismMonicFrobeniusTensorAlgebra

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "Ft" => Rp ⊗[Rv] Mv
local notation "Et" => powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv W hW f

/-- 概要：実テンソルに元の mod p 無限根環の代数作用を与える。
方針：実テンソル同型の逆で標準入力係数射を戻す。
規約：次の係数・根変数公式で自然性を確認する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 pd 源の係数作用。 -/
@[instance_reducible] def powerRootPrismMonicFrobeniusTensorInputAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    Algebra Np Ft := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  exact ((Et hf).symm.toRingHom.comp (algebraMap Np Dp)).toAlgebra

/-- 概要：実テンソル比較は同じ無限根環上の代数同型。
方針：逆同型で戻した作用と順逆の合成を照合する。
規約：元の Rp 代数同型と同じ環同型を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分冪包の普遍性の移送。 -/
def powerRootPrismMonicFrobeniusTensorInputAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    Ft ≃ₐ[Np] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  refine { (Et hf).toRingEquiv with commutes' := ?_ }
  intro r
  exact (Et hf).apply_symm_apply (algebraMap Np Dp r)

/-- 概要：実テンソルの入力環作用は元の Rp 係数作用と一致する。
方針：実テンソル同型の単射性と係数作用の塔を使う。
規約：Rp の任意の元を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な底環作用。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgebra_coeff
    (hf : f.Monic) (r : Rp) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft (algebraMap Rp Np r) = algebraMap Rp Ft r := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  let q := powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np Ft (algebraMap Rp Np r)) =
        algebraMap Np Dp (algebraMap Rp Np r) := q.commutes _
    _ = algebraMap Rp Dp r := (IsScalarTower.algebraMap_apply Rp Np Dp r).symm
    _ = q (algebraMap Rp Ft r) := ((Et hf).commutes r).symm

/-- 概要：第 n 入力根変数は元の第 n+1 根変数の標準像とのテンソル。
方針：実比較の単射性と検証済みの根変数公式を使う。
規約：全段 n で同じ自然な根の族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力環作用の自然性。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgebra_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) = (1 : Rp) ⊗ₜ[Rv] m := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  let q := powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np Ft (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n)) =
        algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) := q.commutes _
    _ = q ((1 : Rp) ⊗ₜ[Rv] m) :=
      (powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable W hW f hf n).symm

/-- 概要：通常多項式の入力像は元の第一根変数のテンソルで評価した値。
方針：評価と環射の可換性に、自然な係数作用と第零入力変数の公式を使う。
規約：任意の Rp 係数多項式を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の f の入力を実テンソルで明示する。 -/
theorem powerRootPrismMonicFrobeniusTensorInputAlgebra_polynomial
    (hf : f.Monic) (g : Polynomial Rp) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 1)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    algebraMap Np Ft (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp g) =
      g.eval₂ (algebraMap Rp Ft) ((1 : Rp) ⊗ₜ[Rv] m) := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp 1)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  let q := powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf
  change algebraMap Np Ft
    (g.eval₂ (algebraMap Rp Np) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp 0)) = _
  exact principalPDSourcePolynomialEvaluation zp q
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp 0) ((1 : Rp) ⊗ₜ[Rv] m)
    (fun r => (Et hf).commutes r)
    (fun r => (IsScalarTower.algebraMap_apply Rp Np Dp r).symm)
    (powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable W hW f hf 0) g

/-- 概要：元の Rp 係数作用・無限根作用・実テンソル作用は作用の塔をなす。
方針：全係数での代数射の一致を使う。
規約：元の二つの作用を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用の整合性。 -/
theorem powerRootPrismMonicFrobeniusTensorInputScalarTower (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := (evp).toRingHom.toAlgebra
    let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
    IsScalarTower Rp Np Ft := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := (evp).toRingHom.toAlgebra
  let := powerRootPrismMonicFrobeniusTensorInputAlgebra W hW f hf
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  exact (powerRootPrismMonicFrobeniusTensorInputAlgebra_coeff W hW f hf r).symm

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicFrobeniusTensorAlgebra

/-! ## André 自然な Frobenius テンソルの PD 入力とイデアル

## 概要

自然な Frobenius テンソルにおける標準入力環作用、比較同型、分冪イデアルを保持する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の元の入力と同じ台環を使う。

## 方針

係数と根変数を保つ比較同型により入力作用と指定イデアルを作る。
原典とは異なる半線形比較・通常テンソルを使う経路。

## 規約

不要になった hpR 付きの分冪構造・分冪射・分冪公式・普遍性の4宣言を削除した。
対応する `_of_unconditional` 版を集約から公開し、モニック性を保持して正次数は追加しない。

## 使われ方

無条件の分冪構造を、同じ元の実引戻しと同じ入力作用に関して適用する。
-/

@[expose] public noncomputable section PowerRootPrismMonicFrobeniusTensorPD

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の台イデアル。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪包の入力条件。 -/
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

end PowerRootPrismMonicFrobeniusTensorPD

/-! ## A 全体の Frobenius 引戻しと実 pd 表示

## 概要

自然な実 Hodge–Tate ϖ 商を A 全体の Frobenius に沿って引き戻すと、
元の f の mod p 入力の主分冪表示と左 A 代数同型になる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の φ_A 引戻しの通常テンソルによる比較。

## 方針

自然な A 係数射を確認し、剰余比較の係数公式を A の半線形性へ持ち上げる。
原典とは異なる半線形環同型と実テンソルの普遍性による経路。

## 規約

左の A を同じ宇宙の TensorBaseCopy A で区別し、左への A 作用を Frobenius とする。
比較先の係数環は R/p と明示し、絶対 prismatic 源の同定は別工程。

## 使われ方

商環間の係数テンソルだけでなく、A 上の Frobenius 引戻しの根変数と pd 構造を扱う。
-/

@[expose] public noncomputable section PowerRootPrismMonicFullFrobeniusPullback

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "bv" => RingHom.comp (Ideal.Quotient.mk Iv) (Ideal.Quotient.mk W.ideal)
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Ac" => TensorBaseCopy A
local notation "downA" => RingEquiv.toRingHom (tensorBaseCopyRingEquiv A)
local notation "αc" => RingEquiv.trans frob (RingEquiv.symm (tensorBaseCopyRingEquiv A))
local notation "rA" => RingHom.comp (algebraMap Rp Dp) bp
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f

/-- 概要：実 ϖ 商の A 係数射は元の自然な R/ϖ 作用の合成。
方針：二段商係数射と既存の自然な商代数作用を合成する。
規約：Frobenius でねじる前の元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の A 上の実引戻しの右因子。 -/
def powerRootPrismMonicVarpiBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    A →+* Mv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  exact (algebraMap Rv Mv).comp bv

/-- 概要：実 ϖ 商の A 係数射は元の無限根入力射の係数制限と一致する。
方針：自然な基底射の代表元公式と商代数の定義を使う。
規約：元の完備化単位と商射を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の元の A 作用の照合。 -/
theorem powerRootPrismMonicVarpiBaseMap_coeff (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicVarpiBaseMap W hW f a₀ =
      powerRootPrismMonicVarpiInputMap W hW f (algebraMap A P a₀) := by
  let := pdCompletionCommRing L p (jL dP)
  exact congrArg (Ideal.Quotient.mk (Ideal.map φ Iv))
    (powerRootPrismMonicHodgeTateBaseMap_mk W hW f a₀)

/-- 概要：実剰余の半線形比較は A 係数に A 自身の Frobenius を作用させる。
方針：R/ϖ 係数公式と係数商同型の代表元公式を合成する。
規約：モニック性以外の次数・p 正則性仮定は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の A 全体の引戻しに必要な半線形性。 -/
theorem powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff
    (hf : f.Monic) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    U hf (powerRootPrismMonicVarpiBaseMap W hW f a₀) = rA ((frob) a₀) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  change U hf (algebraMap Rv Mv (bv a₀)) = _
  rw [powerRootPrismMonicVarpiFrobeniusResidueEquiv_coeff]
  exact congrArg (algebraMap Rp Dp)
    (perfectPrismVarpiFrobeniusQuotientEquiv_mk W hW a₀)

local notation "qA" => powerRootPrismMonicVarpiBaseMap W hW f
local notation "At" => Ac ⊗[A] Mv

/-- 概要：A 上の実 Frobenius 引戻しは元の mod p 入力の主分冪表示と左 A 線形同型。
方針：A 係数の半線形性に自己同型に沿うテンソル比較を適用する。
規約：左 A は型の写し、右因子は自然な実 ϖ 商で、A 作用は明示したものを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の φ_A 引戻し全体の実比較。 -/
def powerRootPrismMonicFullFrobeniusPullbackAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    At ≃ₐ[Ac] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  exact automorphismTensorPullbackAlgEquiv frob qA rA (U hf)
    (powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff W hW f hf)

/-- 概要：A 全体の引戻し比較の単純テンソル公式。
方針：自己同型テンソル比較の公式を実剰余へ適用する。
規約：左の係数は元の A の元で指定し、全ての実 ϖ 商元を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の標準係数と自然な根変数の追跡。 -/
theorem powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_tmul (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    ∀ (a₀ : A) (m : Mv),
      powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f hf
        ((⟨a₀⟩ : Ac) ⊗ₜ[A] m) = algebraMap Rp Dp (bp a₀) * U hf m := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  dsimp only
  intro a₀ m
  exact automorphismTensorPullbackAlgEquiv_tmul frob qA rA (U hf)
    (powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff W hW f hf) a₀ m

/-- 概要：A 全体の引戻し比較は元の第 n+1 根変数を第 n 根変数へ送る。
方針：単純テンソル公式で係数 1 を消し、実剰余比較の根変数公式を使う。
規約：元の自然な入力射と全ての段 n を保持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の入力環作用を A 引戻し上で照合する。 -/
theorem powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f hf
      ((1 : Ac) ⊗ₜ[A] m) = algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  have hunit : algebraMap Rp Dp (bp (1 : A)) = 1 :=
    (congrArg (algebraMap Rp Dp) (map_one bp)).trans (map_one (algebraMap Rp Dp))
  calc
    powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f hf
        ((1 : Ac) ⊗ₜ[A] m) = algebraMap Rp Dp (bp (1 : A)) * U hf m :=
      powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_tmul W hW f hf 1 m
    _ = U hf m :=
      (congrArg (fun z : Dp => z * U hf m) hunit).trans (one_mul (U hf m))
    _ = algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) :=
      powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable_succ W hW f hf n

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicFullFrobeniusPullback

/-! ## André A 全体の Frobenius 引戻しの PD 入力とイデアル

## 概要

A 全体の Frobenius 引戻しにおける標準入力環作用、比較同型、分冪イデアルを保持する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の元の入力と同じ台環を使う。

## 方針

係数と根変数を保つ比較同型により入力作用と指定イデアルを作る。
原典とは異なる半線形比較・通常テンソルを使う経路。

## 規約

不要になった hpR 付きの分冪構造・分冪射・分冪公式・普遍性の4宣言を削除した。
対応する `_of_unconditional` 版を集約から公開し、モニック性を保持して正次数は追加しない。

## 使われ方

無条件の分冪構造を、同じ元の実引戻しと同じ入力作用に関して適用する。
-/

@[expose] public noncomputable section PowerRootPrismMonicFullFrobeniusPD

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "bv" => RingHom.comp (Ideal.Quotient.mk Iv) (Ideal.Quotient.mk W.ideal)
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Ac" => TensorBaseCopy A
local notation "downA" => RingEquiv.toRingHom (tensorBaseCopyRingEquiv A)
local notation "αc" => RingEquiv.trans frob (RingEquiv.symm (tensorBaseCopyRingEquiv A))
local notation "rA" => RingHom.comp (algebraMap Rp Dp) bp
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f

local notation "qA" => powerRootPrismMonicVarpiBaseMap W hW f
local notation "At" => Ac ⊗[A] Mv
local notation "Ef" => powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f

/-- 概要：A 全体の実引戻しに元の mod p 無限根環の代数作用を与える。
方針：A 全体の実引戻し同型の逆で標準入力係数射を戻す。
規約：次の係数・根変数公式で自然性を確認する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 pd 源の係数作用。 -/
@[instance_reducible] def powerRootPrismMonicFullFrobeniusInputAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    Algebra Np At := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  exact ((Ef hf).symm.toRingHom.comp (algebraMap Np Dp)).toAlgebra

/-- 概要：A 全体の実引戻し比較は同じ無限根環上の代数同型。
方針：逆同型で戻した作用と順逆の合成を照合する。
規約：元の左 A 代数同型と同じ環同型を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分冪包の普遍性の移送。 -/
def powerRootPrismMonicFullFrobeniusInputAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    At ≃ₐ[Np] Dp := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  refine { (Ef hf).toRingEquiv with commutes' := ?_ }
  intro r
  exact (Ef hf).apply_symm_apply (algebraMap Np Dp r)

/-- 概要：入力環作用の元の A 係数像は左 A の標準係数像と一致する。
方針：比較の単射性・入力係数の可換性・左 A 線形性を使う。
規約：A の全係数元について二つの作用の一致を述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の元の多項式の係数を保持する。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgebra_base_coeff
    (hf : f.Monic) (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    algebraMap Np At (algebraMap Rp Np (bp a₀)) =
      algebraMap Ac At (⟨a₀⟩ : Ac) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  let q := powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np At (algebraMap Rp Np (bp a₀))) =
        algebraMap Np Dp (algebraMap Rp Np (bp a₀)) := q.commutes _
    _ = algebraMap Rp Dp (bp a₀) := (IsScalarTower.algebraMap_apply Rp Np Dp (bp a₀)).symm
    _ = q (algebraMap Ac At (⟨a₀⟩ : Ac)) := ((Ef hf).commutes (⟨a₀⟩ : Ac)).symm

/-- 概要：第 n 入力根変数は元の第 n+1 根変数の標準像とのテンソル。
方針：入力環同型の単射性と A 全体の引戻しの根変数公式を使う。
規約：選び直した根ではなく元の入力射の像を使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の自然な無限根入力環作用。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgebra_variable
    (hf : f.Monic) (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let m := powerRootPrismMonicVarpiInputMap W hW f
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    algebraMap Np At (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) = (1 : Ac) ⊗ₜ[A] m := by
  let := pdCompletionCommRing L p (jL dP)
  let m := powerRootPrismMonicVarpiInputMap W hW f
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable A p hp (n + 1))
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  let q := powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf
  apply q.injective
  calc
    q (algebraMap Np At (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n)) =
        algebraMap Np Dp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialVariable Rp p hp n) := q.commutes _
    _ = q ((1 : Ac) ⊗ₜ[A] m) :=
      (powerRootPrismMonicFullFrobeniusPullbackAlgEquiv_variable W hW f hf n).symm

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf

/-- 概要：A 全体の実引戻しの分冪イデアルは標準正次数イデアルの逆像。
方針：自然な入力環上の代数同型の逆で像イデアルを取る。
規約：元の A 全体の実引戻し環を維持する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の台イデアル。 -/
def powerRootPrismMonicFullFrobeniusPDIdeal :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    Ideal At := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceIdeal zp Ein

/-- 概要：自然な A 全体の実引戻しの分冪イデアルは元の入力の像を含む。
方針：係数を保つ同型の源への入力所属の一般公式を使う。
規約：モニック性のみを仮定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪包の入力条件。 -/
theorem powerRootPrismMonicFullFrobeniusPDIdeal_input_mem :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    algebraMap Np At zp ∈ powerRootPrismMonicFullFrobeniusPDIdeal W hW f hf := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceIdeal_base_mem zp Ein

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicFullFrobeniusPD

/-! ## 追加正則性なしの実 Frobenius 引戻しの pd 普遍性

## 概要

A 全体の自然な実 Frobenius 引戻しは、モニック性のみの下で元の mod p 入力の実 pd 包となる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の φ_A 引戻しの pd 比較から prism 商の p 正則性を除く。

## 方針

射影的な正次数商を使って構成した比較先の実分冪構造を、検証済みの自然な入力環同型で戻す。
原典とは異なる線形切断・半線形比較・通常テンソル・実分冪構造の移送による証明。

## 規約

完全 prism とモニック性のみを要求する。原典の係数表記との最終照合と絶対 prismatic 源の同定は別工程。

## 使われ方

実 Frobenius 引戻しそのものから、追加正則性なしに任意の分冪標的への一意な射を得る。
-/

@[expose] public noncomputable section PowerRootPrismMonicFullFrobeniusPDOfMonic

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
open _root_.SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : R)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dp" => PrincipalDPPresentation Np zp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "Mv" => T ⧸ Ideal.map φ Iv

local notation "bv" => RingHom.comp (Ideal.Quotient.mk Iv) (Ideal.Quotient.mk W.ideal)
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Ac" => TensorBaseCopy A
local notation "downA" => RingEquiv.toRingHom (tensorBaseCopyRingEquiv A)
local notation "αc" => RingEquiv.trans frob (RingEquiv.symm (tensorBaseCopyRingEquiv A))
local notation "rA" => RingHom.comp (algebraMap Rp Dp) bp
local notation "U" => powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f

local notation "qA" => powerRootPrismMonicVarpiBaseMap W hW f
local notation "At" => Ac ⊗[A] Mv
local notation "Ef" => powerRootPrismMonicFullFrobeniusPullbackAlgEquiv W hW f

variable (hf : f.Monic)
local notation "Ein" => powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf

/-- 概要：自然な A 全体の実引戻し上に元の mod p 入力の実分冪構造を与える。
方針：係数を保つ実同型に沿って比較先の構造を戻す。
規約：prism 商の p 正則性・正次数を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def powerRootPrismMonicFullFrobeniusDividedPowersOfMonic :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    DividedPowers (powerRootPrismMonicFullFrobeniusPDIdeal W hW f hf) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers zp Ein
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf)

/-- 概要：A 全体の実引戻し比較は元の実分冪構造を比較先へ保つ。
方針：同型の源へ戻した構造の分冪射性を使う。
規約：同じ入力環作用と同じイデアルを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 比較。 -/
theorem powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphismOfMonic :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    (powerRootPrismMonicFullFrobeniusDividedPowersOfMonic W hW f hf).IsDPMorphism
      (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf) (Ein).toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceEquiv_isDPMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf)

/-- 概要：自然な入力元の全分冪は標準分冪生成元の実同型による逆像。
方針：比較先の標準分冪値を係数を保つ同型で戻す。
規約：零次数を含む全次数 n を指定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪値の同定。 -/
theorem powerRootPrismMonicFullFrobeniusDividedPowersOfMonic_input_apply
    (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    (powerRootPrismMonicFullFrobeniusDividedPowersOfMonic W hW f hf).dpow n
      (algebraMap Np At zp) = (Ein).symm (principalDPGenerator zp n) := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact principalPDSourceDividedPowers_base_apply zp Ein
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf)
    (powerRootPrimeFrobeniusDividedPowersOfMonic_base_apply W hW f hf) n

/-- 概要：自然な実 Frobenius テンソルは元の mod p 入力の pd 包の普遍性を持つ。
方針：同じ入力環上の代数同型で標準主分冪包の普遍性を移す。
原典とは異なる半線形比較・通常テンソル・実分冪構造の移送による証明。
規約：標的の宇宙・ねじれ・完備性は制約しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実引戻し側の pd 包性。 -/
theorem existsUnique_powerRootPrismMonicFullFrobeniusPDMorphismOfMonic
    {B : Type w} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    let := pdCompletionCommRing L p (jL dP)
    let := (qA).toAlgebra
    let := (RingHom.comp rA downA).toAlgebra
    let := (αc).toRingHom.toAlgebra
    let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
    ∃! F : At →ₐ[Np] B,
      (powerRootPrismMonicFullFrobeniusDividedPowersOfMonic W hW f hf).IsDPMorphism
        Ht F.toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := (qA).toAlgebra
  let := (RingHom.comp rA downA).toAlgebra
  let := (αc).toRingHom.toAlgebra
  let := powerRootPrismMonicFullFrobeniusInputAlgebra W hW f hf
  exact existsUnique_principalPDSourceMorphism zp Ein
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf)
    (powerRootPrimeFrobeniusDividedPowersOfMonic_base_apply W hW f hf) Ht hzB

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicFullFrobeniusPDOfMonic
