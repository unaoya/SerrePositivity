module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedDeltaSourcePrimeCone
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.SaturatedLocalizationTorsion

/-!
# 元の実源の p 錐の分母冪ねじれ

## 概要
BS Rem 7.15（著者版 p.62）の元の実源の p 錐の非零次ホモロジーは、分母冪ねじれ。

## 方針
元の安定係数局所化後の p 錐の純性と、p 錐ホモロジー上で p が零であることを使う。

## 規約
元の実二因子導来源を用い、prism 商の p 正則性を要求しない。

## 使われ方
完備化側の純性と合わせて、元の raw 源の p 正則性を検出する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "XA" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule (deltaDivisionSourceEval D a)),
    boundedAboveDerivedSingleFunctor.obj
      (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)))
attribute [local instance] MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 800000 in
-- 元の二つの実係数作用と、同じ源の実 p 錐・局所化モデルを同時に照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：元の実源の先行 p 錐の各非零次ホモロジー元は、元の分母の冪で零になる。
方針：実安定局所化の消滅を核判定へ渡し、p 錐上の p 零化で元の分母冪へ戻す。
規約：係数環上の p 正則性だけを仮定し、モニック性・完備性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の源の完備化純性との合流。 -/
theorem unconditionalSourcePrimeCone_homology_power_torsion
    (hp : IsSMulRegular A (p : A)) (i : ℤ) (hi : i ≠ 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat LA) i).obj
      ((derivedScalarConeFunctor LA (p : LA)).obj (XA).obj)) :
    ∃ n : ℕ, (MvPolynomial.C d : LA) ^ n • x = 0 := by
  let T := D.frobeniusDenominators (Submonoid.powers d)
  let B := Localization T
  let LB := RelativeFreeDeltaRing (R := B) σ
  letI : IsLocalization ((T).map (MvPolynomial.C : A →+* LA).toMonoidHom) LB := by
    change IsLocalization ((T).map (MvPolynomial.C : A →+* LA)) LB
    exact MvPolynomial.isLocalization T B
  exact (unconditionalSaturatedScalarCone_homology_power_torsion (R := LA)
    D d MvPolynomial.C XA LB i
    (unconditionalDeltaSourcePrimeCone_localization_homology_isZero D d a B hp i hi) x)

end SerrePositivity.BhattScholze.Andre
