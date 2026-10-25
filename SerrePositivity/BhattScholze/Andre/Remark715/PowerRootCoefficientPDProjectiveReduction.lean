module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootCoefficientPDRegularReduction
public import SerrePositivity.BhattScholze.Andre.Remark715.DividedPowerProjectiveCoefficientQuotient

/-!
# André E1・E2：モニック入力の実 pd 包の任意係数還元

## 概要

完全 prism 上の無限根モニック入力の実 pd 包は、任意の mod p 係数元で還元しても
実分冪構造を持つ。BS Rem 7.15(1)（著者版 p.62）の係数変更。

## 方針

正次数商の係数環上の自由性から射影性を得て、係数主イデアルとの交わりを制御する。
原典とは異なる線形切断による分冪降下を使う。

## 規約

還元する係数元にも prism 商にも正則性を要求しない。入力のモニック性は保持する。

## 使われ方

ϖ 持上げによる還元を、prism 商の p 正則性を使わずに構成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "N" => PowerRootPolynomial R p hp
local notation "z" f => powerRootCoefficientPDInput p f
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "J" f => principalDPPositiveIdeal (z f)

/-- 概要：無限根モニック pd 包の構造は任意係数元の商へ降りる。
方針：正次数商の自由性から射影性を供給し、一般の係数商の実分冪構造を使う。
規約：係数元の正則性も prism 商の p 正則性も仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック入力の無条件の係数還元。 -/
def powerRootCoefficientPDReductionOfMonic
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) :
    DividedPowers ((J f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a}))) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  exact dividedPowersQuotientOfProjectiveCoefficient
    (powerRootCoefficientDividedPowers p W hW f hf) a

/-- 概要：任意係数還元後の入力元の分冪は元の標準生成元の商像。
方針：係数商の分冪評価と還元前の入力分冪の公式を合成する。
規約：全次数 n を含み、係数元には制約しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の還元後の pd 普遍性への入力。 -/
theorem powerRootCoefficientPDReductionOfMonic_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (n : ℕ) :
    (powerRootCoefficientPDReductionOfMonic p W hW f hf a).dpow n
      (Ideal.Quotient.mk _ (algebraMap N (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  unfold powerRootCoefficientPDReductionOfMonic
  rw [dividedPowersQuotientOfProjectiveCoefficient_apply _ _ n
    (principalDPPositiveIdeal_base_mem (z f)), powerRootCoefficientDividedPowers_base_apply]

/-- 概要：任意係数元によるモニック pd 包の標準商射は分冪射。
方針：射影的な正次数商を使う分冪商の互換性を適用する。
規約：還元前と還元後の実分冪構造を使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の任意係数還元の構造比較。 -/
theorem powerRootCoefficientPDReductionOfMonic_isDPMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (powerRootCoefficientPDReductionOfMonic p W hW f hf a)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a})) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  exact dividedPowersQuotientOfProjectiveCoefficient_isDPMorphism
    (powerRootCoefficientDividedPowers p W hW f hf) a

end SerrePositivity.BhattScholze.Andre
