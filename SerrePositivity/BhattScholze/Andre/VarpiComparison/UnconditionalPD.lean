module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.PDBaseChange
public import SerrePositivity.BhattScholze.Andre.Unconditional.MonicPDEnvelope
public import SerrePositivity.BhattScholze.Andre.Unconditional.VarpiPDReduction

/-!
# BS Rem 7.15（著者版 p.62）：正則性を追加しない係数テンソルの分冪構造

## 概要
R/ϖ への通常テンソル底変換に分冪構造と自然な分冪射を与える。

## 方針
射影的な正次数商から得た無条件の分冪降下を、既存の係数環同型で移送する。

## 規約
完全 prism とモニック入力を固定し、prism 商の p 正則性を仮定しない。
旧名は保持する。

## 使われ方
A1-c2 の係数比較を原典の実 pd 包として照合する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open scoped TensorProduct
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 概要：分冪構造の環同型による移送は分冪射を与える。
方針：移送された分冪演算の計算公式を用いる。
規約：任意の環同型と分冪イデアルについて成立する。
使われ方：BS Rem 7.15（著者版 p.62）の二つの構造移送を合成する補助。 -/
private theorem transport_isDPMorphism {B C : Type u} [CommRing B] [CommRing C]
    {I : Ideal B} {J : Ideal C} (e : B ≃+* C) (h : I.map e.toRingHom = J)
    (H : DividedPowers I) : H.IsDPMorphism (DividedPowers.ofRingEquiv h H) e.toRingHom := by
  refine ⟨h.le, ?_⟩
  intro n b hb
  exact DividedPowers.ofRingEquiv_dpow_apply h H

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "x" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "Q" => R₀ ⧸ Ideal.span {x}
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

local notation "K" => Ideal.span {algebraMap R₀ D x}

/-- 概要：係数テンソルに追加正則性なしの分冪構造を与える。
方針：無条件の native 分冪構造を環同型で戻す。
規約：正次数イデアルは同型による像として固定する。
使われ方：BS Rem 7.15（著者版 p.62）の実 pd 底変換。 -/
def perfectPrismPDTensorVarpiDividedPowers_of_unconditional
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    DividedPowers ((principalDPPositiveIdeal zv).map
      (perfectPrismPDTensorVarpiEquiv W hW f).symm.toRingHom) := by
  let := varpiCoefficientAlgebra W hW
  exact DividedPowers.ofRingEquiv rfl
    (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf)

/-- 概要：底変換した実分冪構造で、入力の分冪は還元前の標準生成元の像になる。
方針：環同型の移送公式と全標準生成元の一致を使う。
規約：モニック性のみを使い、prism 商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包としての底変換の具体的計算。 -/
theorem perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional
    (hf : f.Monic) (i : ℕ) :
    let := varpiCoefficientAlgebra W hW
    (perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf).dpow i
      (1 ⊗ₜ[R₀] algebraMap (PowerRootPolynomial R₀ p hp) D (powerRootCoefficientPDInput p f)) =
        1 ⊗ₜ[R₀] principalDPGenerator (powerRootCoefficientPDInput p f) i := by
  let := varpiCoefficientAlgebra W hW
  let e := perfectPrismPDTensorVarpiEquiv W hW f
  change e.symm ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow i
    (e (1 ⊗ₜ[R₀] algebraMap (PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)))) = _
  have hInput : e (1 ⊗ₜ[R₀] algebraMap (PowerRootPolynomial R₀ p hp) D
      (powerRootCoefficientPDInput p f)) = algebraMap Nv Dv zv := by
    simpa only [principalDPGenerator_one] using perfectPrismPDTensorVarpiEquiv_generator W hW f 1
  rw [hInput, perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional]
  apply e.injective
  rw [e.apply_symm_apply]
  exact (perfectPrismPDTensorVarpiEquiv_generator W hW f i).symm

/-- 概要：元の実 pd 包から係数テンソルへの標準射は分冪を保つ。
方針：無条件の係数還元の分冪射と二つの構造移送を合成する。
規約：全ての元で includeRight と照合し、hpR を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の pd 底変換の構造射。 -/
theorem perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional
    (hf : f.Monic) :
    let := varpiCoefficientAlgebra W hW
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf)
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
    (perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf) ht hmid
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
