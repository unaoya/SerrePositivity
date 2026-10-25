module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedEvaluationModule
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.LocalizedDeltaSourceTarget

/-!
# 実自由 δ 源の左評価因子と係数局所化の比較

## 概要
BS Rem 7.15（著者版 p.62）の実評価作用を、Frobenius 安定係数局所化へ運ぶ。

## 方針
評価射の係数射との可換性と、分母係数の像を一般加群局所化へ供給する。

## 規約
元の分子の像と標準係数拡大を保持する。

## 使われ方
元の二因子導来源の局所化比較の左因子を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

/-- 概要：実源評価は、分子を同じ係数 δ 射で移す操作と可換。
方針：係数と全 δ 座標で計算し、δ 保存性を反復する。
規約：係数射の単射性・平坦性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の局所化後の左因子の作用。 -/
theorem unconditionalDeltaSourceEvaluation_natural
    {B : Type u} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    (q : A →+* B) (hq : D.IsDeltaHom E q) (a : σ → A) :
    (deltaDivisionSourceEval E (fun s => q (a s))).comp (MvPolynomial.map q) =
      q.comp (deltaDivisionSourceEval D a) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [RingHom.comp_apply, deltaDivisionSourceEval_C]
  · rintro ⟨s, n⟩
    simp only [RingHom.comp_apply, MvPolynomial.map_X, deltaDivisionSourceEval_X]
    exact ((show Function.Semiconj q D.delta E.delta from hq).iterate_right n (a s)).symm

variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実源の左評価因子の標準係数拡大は、局所化 δ 源の評価因子。
方針：元の評価射の可換性と分母像の同定を、加群局所化比較へ渡す。
規約：元の分子族の像と標準多項式係数射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の実二因子導来源の局所化比較。 -/
def unconditionalDeltaSourceEvaluationLocalizationEquiv :
    (ModuleCat.extendScalars (MvPolynomial.map (algebraMap A B))).obj
        (baseChangeScalarModule (deltaDivisionSourceEval D a)) ≃ₗ[LB]
      baseChangeScalarModule (deltaDivisionSourceEval E (fun s => algebraMap A B (a s))) := by
  let φ := deltaDivisionSourceEval D a
  let ψ := deltaDivisionSourceEval E (fun s => algebraMap A B (a s))
  have hcomm : ψ.comp (algebraMap LA LB) = (algebraMap A B).comp φ :=
    unconditionalDeltaSourceEvaluation_natural D E (algebraMap A B)
      (D.isDeltaHom_localization T B
        (D.frobeniusDenominators_stable (Submonoid.powers d))) a
  let M := (T).map (MvPolynomial.C : A →+* LA)
  have hmap : M.map φ.toMonoidHom = T := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      obtain ⟨r, hr, rfl⟩ := hz
      change φ (MvPolynomial.C r) = x at hzx
      rw [deltaDivisionSourceEval_C] at hzx
      exact hzx ▸ hr
    · intro hx
      exact ⟨MvPolynomial.C x, ⟨x, hx, rfl⟩, deltaDivisionSourceEval_C D a x⟩
  have : IsLocalization (M.map φ.toMonoidHom) B := hmap.symm ▸ inferInstance
  exact unconditionalEvaluationLocalizationEquiv φ ψ hcomm M

end SerrePositivity.BhattScholze.Andre
