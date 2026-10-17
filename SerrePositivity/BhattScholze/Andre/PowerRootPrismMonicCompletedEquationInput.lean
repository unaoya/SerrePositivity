module

public import SerrePositivity.BhattScholze.Andre.PowerRootEquationCompletionUniversal
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicEquationInput

/-!
# André A1-a：方程式商の p 完備化からの入力射

## 概要

通常の方程式商の p 完備化から有界試験 prism の商への射を与えると、
実完備化 H から試験 prism への基底と入力根を保つ δ 射が一意に存在する。
BS Rem 7.15（著者版 p.62）の完備入力の試験射への接続。

## 方針

完備入力射を通常の商へ制限し、構成済みの一意な δ 射を使う。
原典とは異なる通常の商・完備化の普遍性と根列持上げによる経路。

## 規約

入力は通常の商を先に p 完備化した環。原典の完備多項式環を割る順序との交換は別工程。
源 H 自体の prism 性や絶対 envelope 全体の同定はまだ主張しない。

## 使われ方

p 完備な試験環への入力射を H の普遍性に渡す。
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
variable (f : Polynomial A)
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


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "S" => PowerRootEquationQuotient p hp fR
local notation "cS" => powerRootEquationQuotientCoeff p hp fR
local notation "rS" => powerRootEquationQuotientRoot p hp fR

local notation "C" => AdicCompletion (Ideal.span {(p : S)}) S
local notation "jS" => algebraMap S C

/-- 概要：方程式商の p 完備化からの入力射を保つ H の δ 射は一意に存在。
方針：入力射を通常の商へ制限して一意な実完備化の射を作る。
規約：入力の完備化を明示し、H 自体の prism 性は別工程。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力環の試験射。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_completed_equation_input
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q) (η : C →+* B ⧸ Q.ideal)
    (hη : (η.comp jS).comp cS = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = η (jS (rS n)) := by
  exact existsUnique_powerRootPrismMonicCompletionHom_of_equation_input W hW f Q hB k
    (η.comp jS) hη

end SerrePositivity.BhattScholze.Andre
