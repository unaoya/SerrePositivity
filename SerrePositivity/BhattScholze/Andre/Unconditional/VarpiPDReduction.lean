module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiRegular
public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientPDProjectiveReduction

/-!
# ϖ 持上げによる分冪還元の hpR 解消

## 概要
BS Rem 7.15(1)（著者版 p.62）のモニック入力について、prism 商の p 正則性なしに分冪を降下する。

## 方針
コミット 4c97d497 の射影的正次数商の線形切断を使い、元の還元環と元の入力を保つ。

## 使われ方
既存 PerfectPrismVarpiRegular の三つの分冪宣言を置換するための別名の受渡し。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "z" f => powerRootCoefficientPDInput p f
local notation "J" f => principalDPPositiveIdeal (z f)

/-- 概要：原典の ϖ の持上げで還元した無限根 pd 包に実分冪構造を与える。
方針：モニック正次数商の射影性により任意係数元の降下を適用する。
規約：f のモニック性のみを仮定し、prism 商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ への係数変更。 -/
def perfectPrismVarpiPowerRootDividedPowers_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    DividedPowers ((J f).map
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))}))) :=
  powerRootCoefficientPDReductionOfMonic p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))

/-- 概要：ϖ 還元後の入力元の分冪は標準分冪生成元の商像。
方針：一般射影的係数還元の計算公式を具体的な持上げに適用する。
規約：全次数を含み、還元前と同じ入力元を使う。
使われ方：BS Rem 7.15（著者版 p.62）の pd 普遍射の照合。 -/
theorem perfectPrismVarpiPowerRootDividedPowers_base_apply_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf).dpow n
      (Ideal.Quotient.mk _ (algebraMap
        (PowerRootPolynomial R₀ p (Nat.Prime.pos (Fact.out : p.Prime))) (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  unfold perfectPrismVarpiPowerRootDividedPowers_of_unconditional
  exact powerRootCoefficientPDReductionOfMonic_base_apply p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)) n

/-- 概要：ϖ の持上げによる商への標準射は分冪を保つ。
方針：一般射影的係数還元の分冪射の定理を使う。
規約：分冪イデアルは正次数イデアルの実商像。
使われ方：BS Rem 7.15（著者版 p.62）の係数還元の構造射。 -/
theorem perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))})) := by
  unfold perfectPrismVarpiPowerRootDividedPowers_of_unconditional
  exact powerRootCoefficientPDReductionOfMonic_isDPMorphism p W hW f hf
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))

end SerrePositivity.BhattScholze.Andre
