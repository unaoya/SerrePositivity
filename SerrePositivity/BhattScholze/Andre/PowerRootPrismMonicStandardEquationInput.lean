module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateRoot
public import SerrePositivity.BhattScholze.Andre.PowerRootEquationQuotient

/-!
# André A1-a：通常の入力環から H/d への標準射

## 概要

通常の方程式商 (A/d)[Y^(1/p^∞)]/(f) を、元の実完備化の分母商 H/d へ送る。
全根変数と係数を自然な標準像へ写す。BS Rem 7.15（著者版 p.62）の入力作用。

## 方針

元の無限根変数の像は互換根列をなし、raw 関係により第零根が f を消す。
通常の方程式商の普遍性で標準射を構成する。原典を補う具体的な入力射による経路。

## 規約

モニック性・正次数・prism 商の p 正則性を仮定しない。完備入力への延長は別工程。

## 使われ方

試験射の入力作用の保存を、個々の根の等式から環射の可換性へ移す。
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


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "φ₀" => powerRootPrismMonicHodgeTateBaseMap W hW f

/-- 概要：H/d 内の全ての標準無限根変数の像。
方針：元の根変数を raw 包・実完備化・分母商へ順に写す。
規約：全ての段 n を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の入力の標準根列。 -/
def powerRootPrismMonicHodgeTateRoots (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    T := by
  let := pdCompletionCommRing L p (jL dP)
  exact qH (uL (jL (powerRootPolynomialVariable A p hp n)))

/-- 概要：H/d の標準根列は p 冪に関して互換。
方針：無限根環の関係式を三つの標準環射で写す。
規約：正則性の追加仮定は不要。
使われ方：BS Rem 7.15（著者版 p.62）の入力環の標準作用。 -/
theorem powerRootPrismMonicHodgeTateRoots_pow (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateRoots W hW f (n + 1) ^ p =
      powerRootPrismMonicHodgeTateRoots W hW f n := by
  let := pdCompletionCommRing L p (jL dP)
  exact (map_pow ((qH).comp ((uL).comp jL)) _ _).symm.trans
    (congrArg ((qH).comp ((uL).comp jL)) (powerRootPolynomialVariable_pow A p hp n))

/-- 概要：標準根列の第零根は元の入力多項式の係数商像を消す。
方針：既存の raw 関係による第零根の評価定理を使う。
規約：モニック性・正次数・p 正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の方程式商の降下条件。 -/
theorem powerRootPrismMonicHodgeTateRoots_eval :
    let := pdCompletionCommRing L p (jL dP)
    (fR).eval₂ φ₀ (powerRootPrismMonicHodgeTateRoots W hW f 0) = 0 :=
  powerRootPrismMonicHodgeTateRoot_eval W hW f

/-- 概要：通常の方程式商から元の H/d への標準入力射。
方針：自然な係数射と標準互換根列を方程式商の普遍性に渡す。
規約：標的の通常の p 完備性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の未完備入力作用。 -/
def powerRootPrismMonicEquationInputMap :
    let := pdCompletionCommRing L p (jL dP)
    S₀ →+* T := by
  let := pdCompletionCommRing L p (jL dP)
  exact (existsUnique_powerRootEquationQuotientHom p hp fR φ₀
    (powerRootPrismMonicHodgeTateRoots W hW f)
    (powerRootPrismMonicHodgeTateRoots_pow W hW f)
    (powerRootPrismMonicHodgeTateRoots_eval W hW f)).choose

/-- 概要：標準入力射は係数射と可換。
方針：方程式商の一意存在の係数条件を取り出す。
規約：元の prism 商 R の自然な作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の基底を保つ入力作用。 -/
theorem powerRootPrismMonicEquationInputMap_coeff :
    let := pdCompletionCommRing L p (jL dP)
    (powerRootPrismMonicEquationInputMap W hW f).comp
      (powerRootEquationQuotientCoeff p hp fR) = φ₀ := by
  let := pdCompletionCommRing L p (jL dP)
  exact (existsUnique_powerRootEquationQuotientHom p hp fR φ₀
    (powerRootPrismMonicHodgeTateRoots W hW f)
    (powerRootPrismMonicHodgeTateRoots_pow W hW f)
    (powerRootPrismMonicHodgeTateRoots_eval W hW f)).choose_spec.1.1

/-- 概要：標準入力射は全ての入力根を元の H/d の標準像へ送る。
方針：方程式商の一意存在の根条件を取り出す。
規約：全ての段 n に対する実際の入力像を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の入力射と試験射の可換性。 -/
theorem powerRootPrismMonicEquationInputMap_root (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicEquationInputMap W hW f (powerRootEquationQuotientRoot p hp fR n) =
      powerRootPrismMonicHodgeTateRoots W hW f n := by
  let := pdCompletionCommRing L p (jL dP)
  exact (existsUnique_powerRootEquationQuotientHom p hp fR φ₀
    (powerRootPrismMonicHodgeTateRoots W hW f)
    (powerRootPrismMonicHodgeTateRoots_pow W hW f)
    (powerRootPrismMonicHodgeTateRoots_eval W hW f)).choose_spec.1.2 n

end SerrePositivity.BhattScholze.Andre
