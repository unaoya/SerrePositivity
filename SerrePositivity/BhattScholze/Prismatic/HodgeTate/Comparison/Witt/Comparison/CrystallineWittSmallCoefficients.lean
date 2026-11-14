module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeFrame
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallFrame
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDSmallCoefficientComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDSmallCoefficientComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDEnvelopeAffineBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor

/-!
# 整係数と Witt 係数の小さい橋の可換図式

## 概要
小さい結晶の橋の係数変更を、Witt 結晶基底の有限 affine 枠での橋と照合する。

## 方針
分冪枠の係数変更が δ 構造、基底脚、頂点変数を保つことを使い、
有限 affine 包の普遍性で二つの合成を同一視する。

## 規約
C は p 正則かつ p 進完備。基底射は既存の結晶基底から Witt 環への標準射。

## 使われ方
BS 著者版 Theorem 6.4 の最初の比較を整係数の小さい橋から移す厳密な図式。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C))
variable [hC : IsAdicComplete (Ideal.span {(p : C)}) C] (r n : ℕ)

local notation "k" => crystallineBase p
local notation "W" => WittVector p C
local notation "γK" => crystallineSmallBridgeBasePD p
local notation "γW" => wittPdStructure p C hpC hlocalC
local notation "hpK" => CrystallinePDRetraction.base_prime p
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "hkK" => crystallineBase_complete p
local notation "hkW" => witt_isAdicComplete p C hpC
local notation "hrK" => crystallineBase_regular p
local notation "hrW" => witt_mul_prime_injective p C hpC
local notation "hJK" => PDPolynomialFunctor.base_ker
  (J := Ideal.span {(p : k)}) (Poly.mk r : Poly k)
local notation "hJW" => PDPolynomialFunctor.base_ker
  (J := wittPdIdeal p C) (Poly.mk r : Poly W)
local notation "EK" => crystallineSmallBridgeFrameTarget p r n
local notation "EW" => crystallineWittSmallFrameTarget p C hpC hlocalC r n
local notation "TK" => crystallineSmallBridgeFramePrism p r n
local notation "TW" => crystallineWittSmallFramePrism p C hpC hlocalC r n
local notation "U" => crystallineSmallBridgeAffineTerm p r n

include hpC hC in
/-- 実際の小さい分冪模型の Witt 係数変更。 -/
def crystallineWittSmallModelCoefficient : pdTerm p k r n →+* pdTerm p W r n := by
  let : Algebra (crystallineBase.{u} p) W := (crystallineWittBaseMap p C hpC).toAlgebra
  exact ((pdModelBaseChange p k W r).app ⦋n⦌).right.hom

/-- 実際の整係数の小さい橋を有限 affine 枠の始域で読む。 -/
def crystallineSmallModelBridgeAt :
    (crystallineSmallBridgeAffineTerm.{u} p r n).X.B →+*
      pdTerm p (crystallineBase.{u} p) r n :=
  (crystallineSmallBridgeFrameEquiv.{u} p r n).symm.toRingHom.comp
    (crystallineSmallBridgeFrameMap.{u} p r n)

private def crystallineWittSmallFrameCoefficient : (EK).carrier →+* (EW).carrier := by
  let : Algebra (crystallineBase.{u} p) W := (crystallineWittBaseMap p C hpC).toAlgebra
  exact PDSmallCoefficientComparison.coefficientMap p k W γK γW hpK hpW hkK hkW hrK hrW
    r n hJK hJW

private theorem crystallineWittSmallFrameCoefficient_eq_model :
    crystallineWittSmallFrameCoefficient p C hpC hlocalC r n =
      (crystallineWittSmallFrameEquiv p C hpC hlocalC r n).toRingHom.comp
        ((crystallineWittSmallModelCoefficient p C hpC r n).comp
          (crystallineSmallBridgeFrameEquiv p r n).symm.toRingHom) := by
  let : Algebra (crystallineBase.{u} p) W := (crystallineWittBaseMap p C hpC).toAlgebra
  exact PDSmallCoefficientComparison.coefficientMap_eq_model
    p k W γK γW hpK hpW hkK hkW hrK hrW r n hJK hJW

private theorem crystallineWittSmallFrameCoefficient_delta :
    (TK).deltaStructure.IsDeltaHom (TW).deltaStructure
      (crystallineWittSmallFrameCoefficient p C hpC hlocalC r n) := by
  let : Algebra (crystallineBase.{u} p) W := (crystallineWittBaseMap p C hpC).toAlgebra
  have hφW : (wittPdIdeal p C).map (wittCrystallineDelta hpC).frobeniusLift ≤
      Ideal.span {(p : W)} := by
    rw [wittCrystallineDelta_frobenius]
    exact wittFrobenius_map_pdIdeal
  exact PDSmallCoefficientComparison.coefficientMap_isDeltaHom p k W γK γW hpK hpW
    hkK hkW hrK hrW r n hJK hJW
    (crystallineWittBaseMap_isDPMorphism p C hpC γK hlocalC)
    (crystallineBasePrism p).deltaStructure (wittCrystallineDelta hpC)
    (CrystallinePDRetraction.local_base p)
    (fun m hm => witt_isUnit_natCast p C m (hlocalC m hm))
    (CrystallinePDRetraction.frobenius_base p) hφW
    (crystallineWittBaseMap_isDeltaHom p C hpC)
    (CrystallinePDRetraction.regular p r n)
    (crystallineWittSmallFrame_regular p C hpC hlocalC r n)

variable {κ : Cardinal.{u}} (V : AffineEnvelopeTerm (wittCrystallinePrism hpC) r n κ)

private theorem crystallineWittSmallFrame_square :
    (crystallineWittSmallFrameCoefficient p C hpC hlocalC r n).comp
        (crystallineSmallBridgeFrameMap p r n) =
      (crystallineWittSmallFrameMap p C hpC hlocalC r n V).comp
        (affineEnvelopeCoefficientMap (crystallineWittBaseHom p C hpC) U V) := by
  let : Algebra (crystallineBase.{u} p) W := (crystallineWittBaseMap p C hpC).toAlgebra
  rw [crystallineSmallBridgeFrameMap_eq_affineBridge]
  apply pdEnvelopeAffineBridge_coefficients γK r n EK TK
    (crystallineSmallBridgeFramePrism_generator p r n)
    (crystallineBasePrism p) U (crystallineSmallBridgeFrame_difference_mem p r n)
    γW EW TW (wittPDEnvelopeCrystalline_generator hpC hlocalC EW _)
    (wittCrystallinePrism hpC) V
    (crystallineWittSmallFrame_difference_mem p C hpC hlocalC r n)
    (crystallineSmallBridgeFrameBase p r n)
    (wittPDEnvelopeCrystallineBase hpC hlocalC EW _)
    (crystallineWittBaseHom p C hpC)
    (crystallineWittSmallFrameCoefficient p C hpC hlocalC r n)
    (crystallineWittSmallFrameCoefficient_delta p C hpC hlocalC r n)
  · exact PDSmallCoefficientComparison.coefficientMap_base
      p k W γK γW hpK hpW hkK hkW hrK hrW r n hJK hJW
  · intro j i
    exact PDSmallCoefficientComparison.coefficientMap_variable
      p k W γK γW hpK hpW hkK hkW hrK hrW r n hJK hJW (ULift.up j) i

/-- 整係数の小さい橋と Witt 結晶基底上の小さい橋の厳密な係数変更の図式。 -/
theorem crystallineWittSmallBridgeAt_coefficients :
    (crystallineWittSmallModelCoefficient p C hpC r n).comp
        (crystallineSmallModelBridgeAt p r n) =
      (crystallineWittSmallBridgeAt p C hpC hlocalC r n V).comp
        (affineEnvelopeCoefficientMap (crystallineWittBaseHom p C hpC) U V) := by
  let : Algebra (crystallineBase.{u} p) W := (crystallineWittBaseMap p C hpC).toAlgebra
  apply RingHom.ext
  intro x
  apply (crystallineWittSmallFrameEquiv p C hpC hlocalC r n).injective
  have h := RingHom.congr_fun (crystallineWittSmallFrame_square p C hpC hlocalC r n V) x
  rw [crystallineWittSmallFrameCoefficient_eq_model] at h
  simp only [RingHom.comp_apply] at h
  change crystallineWittSmallFrameEquiv p C hpC hlocalC r n
      (crystallineWittSmallModelCoefficient p C hpC r n
        ((crystallineSmallBridgeFrameEquiv p r n).symm
          (crystallineSmallBridgeFrameMap p r n x))) =
    crystallineWittSmallFrameEquiv p C hpC hlocalC r n
      ((crystallineWittSmallFrameEquiv p C hpC hlocalC r n).symm
        (crystallineWittSmallFrameMap p C hpC hlocalC r n V
          (affineEnvelopeCoefficientMap (crystallineWittBaseHom p C hpC) U V x)))
  rw [AlgEquiv.apply_symm_apply]
  exact h

end SerrePositivity.BhattScholze.Prismatic
