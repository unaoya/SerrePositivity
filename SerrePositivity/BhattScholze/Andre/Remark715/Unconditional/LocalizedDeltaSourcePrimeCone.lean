module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedDeltaSourceTensor
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.SourceUnitSingle
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange

/-!
# 元の実源の p 錐の局所化後の純性

## 概要
BS Rem 7.15（著者版 p.62）の元の実 p 錐は、安定係数局所化後に次数零に集中する。

## 方針
元の実局所化とスカラー錐の比較を、単元分母の元の評価加群の p 正則性へ接続する。

## 規約
必要な p 正則性は係数環上だけであり、prism 商の p 正則性は要求しない。

## 使われ方
元の raw 源の p 錐の負次数を、d 冪ねじれとして検出する。
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
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
local notation "qL" => MvPolynomial.map (σ := σ × ℕ) (algebraMap A B)
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
local notation "XA" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実源の先行 p 錐の局所化後は、全非零次ホモロジーが消える。
方針：元の二因子源の局所化比較と、局所化先の評価加群上の p 正則性を使う。
規約：係数環 A の p 正則性だけを仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw 源の p 正則性検出。 -/
theorem unconditionalDeltaSourcePrimeCone_localization_homology_isZero
    (hp : IsSMulRegular A (p : A)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat LB) i).obj
      ((boundedAboveDerivedBaseChange qL).obj
        ((boundedAboveDerivedScalarCone LA (p : LA)).obj XA)).obj) := by
  letI : Module.Flat A B := IsLocalization.flat B T
  have hpB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using hp.of_flat (S := B)
  have hdB : IsUnit (algebraMap A B d) := IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩
  let e₁ := boundedAboveDerivedBaseChangeScalarConeIso qL (p : LA) XA
  have e₂ := (derivedScalarConeFunctor LB (p : LB)).mapIso
    (DerivedCategory.Minus.ι.mapIso (unconditionalDeltaSourceTensorLocalizationIso D d a B))
  rw [map_natCast] at e₁
  exact (unconditionalSourceUnit_primeCone_homology_isZero E (algebraMap A B d) hdB
    (fun s => algebraMap A B (a s)) hpB i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat LB) i).mapIso (e₁ ≪≫ e₂))

end SerrePositivity.BhattScholze.Andre
