module

public import SerrePositivity.BhattScholze.Andre.PrincipalDPPositiveUniversal

/-!
# André E1・E2：正則 δ 持ち上げの mod p 一次関係商の pd 包普遍性

## 概要

正則な δ 持ち上げから構成した実分冪構造を持つ一次関係商は、
任意の分冪標的への係数を保つ分冪射の一意存在を満たす。
BS Rem 7.15(1)（著者版 p.62）の実 pd 包の普遍性。

## 方針

実分冪構造と、その入力元の分冪が標準生成元に一致する公式を前工程から供給する。

## 規約

持ち上げの p 正則性・p 局所性・δ 構造と、入力元の mod p 正則性は明示する。
分冪構造や値の公式そのものを仮定する必要はない。

## 使われ方

完全 prism 上の正則モニック入力へ適用し、通常の明示表示を実 pd 包へ接続する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：正則な δ 持ち上げの mod p 一次関係商から、任意の分冪標的への分冪射は一意。
方針：既に構成した実分冪構造と標準生成元公式を一般の一次関係商の普遍性へ渡す。
規約：標的の正則性・δ 構造・完備性は要求しない。持ち上げの仮定は明示したまま。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の通常の普遍性。 -/
theorem existsUnique_regularPrincipalModPrimeDPMorphism
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    {B : Type v} [CommRing B] [Algebra (A ⧸ Ideal.span {(p : A)}) B]
    {I : Ideal B} (Ht : DividedPowers I)
    (hyB : algebraMap (A ⧸ Ideal.span {(p : A)}) B
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y) ∈ I) :
    ∃! F : PrincipalDPPresentation (A ⧸ Ideal.span {(p : A)})
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) y) →ₐ[A ⧸ Ideal.span {(p : A)}] B,
      (regularPrincipalModPrimeDividedPowers hlocal hpA D y hy).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _
    (regularPrincipalModPrimeDividedPowers hlocal hpA D y hy)
    (regularPrincipalModPrimeDividedPowers_base_apply hlocal hpA D y hy) Ht hyB

end SerrePositivity.BhattScholze.Andre
