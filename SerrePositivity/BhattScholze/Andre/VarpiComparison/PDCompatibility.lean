module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.PDBaseChange
public import SerrePositivity.BhattScholze.Andre.Unconditional.VarpiPDReduction

/-!
# BS Rem 7.15（著者版 p.62）：自然な係数テンソル射は分冪射

## 概要
実装の A/p 上の実 pd 包から R/ϖ への通常テンソル底変換は分冪演算を保つ。

## 方針
射影的係数商への分冪射と二つの構造移送を合成し、全ての元で自然な射と照合する。
原典の p ねじれなしへの帰着とは異なる証明経路。

## 規約
モニック入力のみを仮定する。標準生成元だけの照合で代用しない。

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
方針：射影的係数商の分冪射を構造移送と合成し、全元で includeRight と同一視する。
規約：元の環と係数作用を保持し、hpR と正次数を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包の底変換を実分冪射として供給する。 -/
theorem perfectPrismPDTensorVarpi_isDPMorphism
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismPDTensorVarpiDividedPowers W hW f hf)
      (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  let e₀ := perfectPrismVarpiPDEnvelopeEquiv W hW f
  have hq := perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional W hW f hf
  have h₀ := transport_isDPMorphism e₀
    (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
  have ht := transport_isDPMorphism e.symm rfl
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)
  have hmid := DividedPowers.IsDPMorphism.comp
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf) h₀ hq
  have hc := DividedPowers.IsDPMorphism.comp
    (perfectPrismPDTensorVarpiDividedPowers W hW f hf) ht hmid
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
