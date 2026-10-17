module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.PDBaseChange

/-!
# BS Rem 7.15（著者版 p.62）：自然な係数テンソル射は分冪射

## 概要
実装の A/p 上の実 pd 包から R/ϖ への通常テンソル底変換は分冪演算を保つ。

## 方針
既存の正則係数商への分冪射と二つの構造移送を合成し、全ての元で自然な射と照合する。

## 規約
モニック入力と prism 商の p 正則性を明示する。標準生成元だけの照合で代用しない。

## 使われ方
原典側の pd 包の普遍性と通常のテンソル底変換の対応を保証する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped TensorProduct
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 分冪構造の環同型による移送は分冪射を与える。BS Rem 7.15（著者版 p.62）への補助。 -/
private theorem transport_isDPMorphism {B C : Type u} [CommRing B] [CommRing C]
    {I : Ideal B} {J : Ideal C} (e : B ≃+* C) (h : I.map e.toRingHom = J)
    (H : DividedPowers I) : H.IsDPMorphism (DividedPowers.ofRingEquiv h H) e.toRingHom := by
  refine ⟨h.le, ?_⟩
  intro n b hb
  exact DividedPowers.ofRingEquiv_dpow_apply h H

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "x" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "K" => Ideal.span {algebraMap R₀ D x}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}

/-- 概要：元の実 pd 包から係数テンソル底変換への標準射は分冪を保つ。
方針：正則係数商の分冪射を構造移送と合成し、全元で includeRight と同一視する。
規約：hpR は既存の正則係数商構成の仮定であり、環同型自体の仮定ではない。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包の底変換を実分冪射として供給する。 -/
theorem perfectPrismPDTensorVarpi_isDPMorphism
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismPDTensorVarpiDividedPowers W hW f hpR hf)
      (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  let e₀ := perfectPrismVarpiPDEnvelopeEquiv W hW f
  have hq := perfectPrismVarpiPowerRootDividedPowers_isDPMorphism W hW hpR f hf
  have h₀ := transport_isDPMorphism e₀
    (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (perfectPrismVarpiPowerRootDividedPowers W hW hpR f hf)
  have ht := transport_isDPMorphism e.symm rfl
    (perfectPrismVarpiNativeDividedPowers W hW f hpR hf)
  have hmid := DividedPowers.IsDPMorphism.comp
    (perfectPrismVarpiNativeDividedPowers W hW f hpR hf) h₀ hq
  have hc := DividedPowers.IsDPMorphism.comp
    (perfectPrismPDTensorVarpiDividedPowers W hW f hpR hf) ht hmid
  have he : (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom =
      e.symm.toRingHom.comp (e₀.toRingHom.comp (Ideal.Quotient.mk K)) := by
    apply RingHom.ext
    intro t
    apply e.injective
    change e (1 ⊗ₜ[R₀] t) = e (e.symm (e₀ (Ideal.Quotient.mk K t)))
    rw [e.apply_symm_apply]
    exact perfectPrismPDTensorVarpiEquiv_one_tmul W hW f t
  rw [← he] at hc
  exact hc

end SerrePositivity.BhattScholze.Andre.VarpiComparison
