module

public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientPDEnvelope
public import SerrePositivity.BhattScholze.Andre.PrincipalDPPositiveQuotient
public import SerrePositivity.BhattScholze.Andre.DividedPowerRegularQuotient

/-!
# André E1・E2：正則係数元による無限根実分冪包の還元

## 概要

無限根環上のモニック入力の正次数分冪商は係数環上自由。
したがって正則な係数元による商に実分冪構造が降りる。
BS Rem 7.15(1)（著者版 p.62）の R/ϖ 係数へ進むための具体的な降下。

## 方針

正次数分冪商を通常のモニック入力商に同定し、既存の無限根モニック商の基底を使う。
係数元の正則性を平坦性で移し、一般の正則元分冪商を適用する。

## 規約

係数環は R=A/(p)。降下する係数元 a の R 内の正則性を明示する。
原典の ϖ との同定はこのファイルだけでは主張しない。

## 使われ方

原典の係数商との比較に際し、補助的なイデアル飽和性を仮定せず実分冪構造を供給する。
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

/-- 概要：係数商上の無限根環の通常モニック入力商は元の係数商上自由。
方針：名前付き入力を展開し、通常のモニック商の既存の基底を実主イデアル商へ移す。
規約：モニック f の正次数は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数分冪商の自由性の入力。 -/
theorem powerRootCoefficientInputQuotient_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free R (N ⧸ Ideal.span {(z f)}) := by
  unfold powerRootCoefficientPDInput
  let := powerRootPolynomialBaseAlgebra R p hp
  have h := powerRootPolynomialQuotient_free R p hp (f.map bar) (hf.map bar)
  change Module.Free R
    (N ⧸ (Ideal.span {f.map bar}).map (algebraMap (Polynomial R) N)) at h
  rw [powerRootPolynomialQuotient_ideal] at h
  exact h

/-- 概要：実無限根 pd 包を正次数分冪イデアルで割った商は係数商 A/(p) 上自由。
方針：正次数商と通常入力商の代数同型を係数へ制限して自由性を戻す。
規約：完全 prism や実分冪構造の存在自体はこの台加群の自由性には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更時の交わりの制御。 -/
theorem powerRootCoefficientPDPositiveQuotient_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free R ((D f) ⧸ J f) := by
  let := powerRootCoefficientInputQuotient_free p f hf
  exact Module.Free.of_equiv
    ((principalDPPositiveQuotientEquiv (z f)).restrictScalars R).symm.toLinearEquiv

/-- 概要：正則な係数元は正次数分冪商でも正則。
方針：正次数商の係数環上の自由性と平坦性で正則性を移す。
規約：正則性は元の係数商 A/(p) に要求する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数元による実分冪降下。 -/
theorem powerRootCoefficientPDPositiveQuotient_regular (f : Polynomial A) (hf : f.Monic)
    (a : R) (ha : IsSMulRegular R a) :
    IsSMulRegular ((D f) ⧸ J f) (Ideal.Quotient.mk (J f) (algebraMap R (D f) a)) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  let : Module.Flat R ((D f) ⧸ J f) := Module.Flat.of_free
  exact ha.of_flat (S := (D f) ⧸ J f)

/-- 概要：完全 prism 上の実無限根 pd 包の構造は正則な係数元による実商へ降りる。
方針：係数元の正次数商上の正則性を供給し、一般の正則元分冪商を適用する。
規約：降下後のイデアルは正次数イデアルの実商射による像。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数 R/ϖ へ進む実分冪構造。 -/
def powerRootCoefficientPDRegularReduction
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) :
    DividedPowers ((J f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a}))) :=
  dividedPowersQuotientOfRegular (powerRootCoefficientDividedPowers p W hW f hf)
    (algebraMap R (D f) a) (powerRootCoefficientPDPositiveQuotient_regular p f hf a ha)

/-- 概要：正則係数元による商の入力元の分冪は標準生成元の商像。
方針：商分冪作用の互換性と還元前の標準分冪値の公式を使う。
規約：全次数 n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更後の pd 普遍性への入力。 -/
theorem powerRootCoefficientPDRegularReduction_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) (n : ℕ) :
    (powerRootCoefficientPDRegularReduction p W hW f hf a ha).dpow n
      (Ideal.Quotient.mk _ (algebraMap N (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  unfold powerRootCoefficientPDRegularReduction
  rw [dividedPowersQuotientOfRegular_apply _ _ _ n (principalDPPositiveIdeal_base_mem (z f)),
    powerRootCoefficientDividedPowers_base_apply]


/-- 概要：正則係数元による実還元の標準商射は分冪射。
方針：一般の正則元分冪商の射の互換性を具体的な実構造に適用する。
規約：元の正次数イデアルと還元後の実像を比較する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更後の普遍射の照合。 -/
theorem powerRootCoefficientPDRegularReduction_isDPMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (powerRootCoefficientPDRegularReduction p W hW f hf a ha)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a})) :=
  dividedPowersQuotientOfRegular_isDPMorphism (powerRootCoefficientDividedPowers p W hW f hf)
    (algebraMap R (D f) a) (powerRootCoefficientPDPositiveQuotient_regular p f hf a ha)

end SerrePositivity.BhattScholze.Andre
