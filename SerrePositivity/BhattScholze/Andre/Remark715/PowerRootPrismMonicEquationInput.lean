module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootEquationQuotient
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicBasePrismUniversal

/-!
# André E1・E2：通常の方程式商からの入力射による実完備化の普遍性

## 概要

通常の入力環 (A/d)[Y^(1/p^∞)]/(f) から試験 prism の商への射を与えると、
実完備化から試験 prism への基底と入力根を保つ δ 射が一意に存在する。
BS Rem 7.15（著者版 p.62）の完備入力環との比較への一段階。

## 方針

入力環の標準根の像から互換根列と方程式を抽出し、一般基底 prism 射の普遍性へ渡す。
原典とは異なる通常の商の明示的な普遍性と根列持上げによる経路。

## 規約

入力環はこの段階では未完備。原典の完備入力環との一致や H の prism 性は主張しない。
モニック性・正次数や源の prism 商の p 正則性を前提としない。

## 使われ方

個々の根列の指定を実際の入力環からの環射に置き換える。
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

/-- 概要：通常の方程式商からの入力射を保つ実完備化の δ 射は一意に存在。
方針：標準根の像が満たす互換性と方程式を一般基底射の普遍性に渡す。
規約：通常の商 S と有界試験 prism を使い、原典の完備 S との同定は別工程。
使われ方：BS Rem 7.15（著者版 p.62）の入力環からの試験データ。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_equation_input
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : OrientedPrism.Hom W Q) (η : S →+* B ⧸ Q.ideal)
    (hη : η.comp cS = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = η (rS n) := by
  have hρ : ∀ n, η (rS (n + 1)) ^ p = η (rS n) := by
    intro n
    exact (map_pow η _ _).symm.trans
      (congrArg η (powerRootEquationQuotientRoot_pow p hp fR n))
  have heq := congrArg η (powerRootEquationQuotientRoot_equation p hp fR)
  rw [Polynomial.hom_eval₂, map_zero, hη, Polynomial.eval₂_map] at heq
  exact existsUnique_powerRootPrismMonicCompletionHom_over_bounded_prism W hW f Q hB k
    (fun n => η (rS n)) hρ heq

end SerrePositivity.BhattScholze.Andre
