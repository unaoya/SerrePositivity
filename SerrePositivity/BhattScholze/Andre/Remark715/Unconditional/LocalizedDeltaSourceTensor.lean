module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedDeltaSourceEvaluation
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.SourceUnitPurity
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import Mathlib.RingTheory.Flat.Localization

/-!
# 元の実二因子 δ 源の係数局所化

## 概要
BS Rem 7.15（著者版 p.62）の元の実導来源を、係数局所化上の実源へ比較する。

## 方針
平坦係数拡大と実導来テンソルの比較に、左右因子の元の係数拡大同型を合成する。

## 規約
分子像・係数射・二つの実源作用を保持する。完備化やねじれ除去を行わない。

## 使われ方
元の実源の局所化側のホモロジー消滅を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
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
local notation "Nβ" => baseChangeScalarModule
  (deltaDivisionSourceEval E (fun s => algebraMap A B (a s)))
local notation "Nα" => baseChangeScalarModule
  (deltaDivisionSourceMap (σ := σ) E (algebraMap A B d))
local notation "XA" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "XB" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Nβ, boundedAboveDerivedSingleFunctor.obj Nα)
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実二因子導来源の標準係数拡大は、局所化上の実二因子源。
方針：平坦な多項式係数局所化と、元の左右因子の標準比較を合成する。
規約：二因子の順序・分子像・標準係数射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の消滅の移送。 -/
def unconditionalDeltaSourceTensorLocalizationIso :
    (boundedAboveDerivedBaseChange qL).obj XA ≅ XB := by
  letI : Module.Flat LA LB :=
    IsLocalization.flat LB ((T).map (MvPolynomial.C : A →+* LA))
  let eβ := (unconditionalDeltaSourceEvaluationLocalizationEquiv D d a B).toModuleIso
  let eα := (unconditionalDeltaSourceTargetLocalizationEquiv (σ := σ) D d B).toModuleIso
  exact boundedAboveDerivedTensorBaseChangeModuleIso qL Mβ Mα
      (scalarExtensionTorVanishing_of_flat_algebra Mβ)
      (scalarExtensionTorVanishing_of_flat_algebra Mα) ≪≫
    boundedAboveDerivedTensor.mapIso
      (Iso.prod (boundedAboveDerivedSingleFunctor.mapIso eβ)
        (boundedAboveDerivedSingleFunctor.mapIso eα))

/-- 概要：元の実導来源の標準局所化後は、全非零次数のホモロジーが消える。
方針：元の導来局所化同型で、単元分母の実源の消滅へ移す。
規約：元の対象を係数拡大したものについて述べる。
使われ方：BS Rem 7.15（著者版 p.62）の raw 源の局所化と完備化による純性検出。 -/
theorem unconditionalDeltaSourceTensor_localization_homology_isZero
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat LB) i).obj
      ((boundedAboveDerivedBaseChange qL).obj XA).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat LB) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (unconditionalDeltaSourceTensorLocalizationIso D d a B))
  exact (unconditionalSourceSaturatedLocalization_homology_isZero D d a B i hi).of_iso e

end SerrePositivity.BhattScholze.Andre
