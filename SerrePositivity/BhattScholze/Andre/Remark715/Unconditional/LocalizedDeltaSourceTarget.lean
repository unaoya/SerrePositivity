module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedScalarModule
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.SourceUnitDenominator
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# 実自由 δ 源の右因子と係数局所化の比較

## 概要
BS Rem 7.15（著者版 p.62）の実源作用を、Frobenius 安定係数局所化へ運ぶ。

## 方針
実係数射との可換性と、分母係数を固定することを一般加群局所化へ供給する。

## 規約
元の実源射と標準多項式係数射を用いる。

## 使われ方
元の二因子導来源の局所化比較の右因子を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A)
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実源の右因子の標準係数拡大は、局所化 δ 源の右因子。
方針：元の実射の可換性と係数上の恒等性を、加群局所化の具体的比較へ渡す。
規約：元の二つのスカラー作用を保持する線形同型。
使われ方：BS Rem 7.15（著者版 p.62）の実導来源の局所化比較。 -/
def unconditionalDeltaSourceTargetLocalizationEquiv :
    (ModuleCat.extendScalars (MvPolynomial.map (algebraMap A B))).obj
        (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) ≃ₗ[LB]
      baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) E (algebraMap A B d)) := by
  let α := deltaDivisionSourceMap (σ := σ) D d
  let β := deltaDivisionSourceMap (σ := σ) E (algebraMap A B d)
  have hcomm : β.comp (algebraMap LA LB) = (algebraMap LA LB).comp α := by
    exact (unconditionalDeltaDivisionSourceMap_natural D E (algebraMap A B)
      (D.isDeltaHom_localization T B
        (D.frobeniusDenominators_stable (Submonoid.powers d))) d).symm
  have hfix (s : (T).map (MvPolynomial.C : A →+* LA)) : α s = s := by
    obtain ⟨r, hr, hs⟩ := s.property
    rw [← hs]
    exact deltaDivisionSourceMap_C D d r
  exact unconditionalScalarModuleLocalizationEquiv α β hcomm
    ((T).map (MvPolynomial.C : A →+* LA)) hfix

end SerrePositivity.BhattScholze.Andre
