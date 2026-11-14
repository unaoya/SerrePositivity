module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeCoordinates
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDEnvelopeAffineBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDEnvelopeAffineBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineBridgeAlgebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallineDivisionEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineBridgeAlgebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeCoordinates
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison

/-!
# 小さい結晶の橋の有限分冪枠での仕様

## 概要
整係数の小さい結晶の橋を、標準の結晶 prism を持つ有限分冪枠への射として読む。

## 方針
既存の完備模型の同型を通し、評価の δ 両立、基底線形性、頂点の p 乗の式を合わせる。

## 規約
余単体の次数は自然数で指定する。既存の橋の定義は変更しない。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 係数変更との厳密な照合。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (r n : ℕ)

/-- 結晶基底の (p) の標準分冪構造。 -/
def crystallineSmallBridgeBasePD : DividedPowers (Ideal.span {(p : crystallineBase.{u} p)}) := by
  exact residuePdStructure p (crystallineBase_regular p) (CrystallinePDRetraction.local_base p)

/-- 小さい結晶の橋の標的となる標準の完備分冪枠。 -/
def crystallineSmallBridgeFrameTarget :
    CompletedPDEnvelopeData p (crystallineSmallBridgeBasePD.{u} p)
      (RingHom.ker (pdFrameEval (k := crystallineBase.{u} p)
        (fun j : ULift.{u} (Fin r) => (MvPolynomial.X j.down :
          MvPolynomial (Fin r) (crystallineBase.{u} p ⧸ Ideal.span {(p : crystallineBase.{u} p)})))
        n)) := by
  exact CrystallinePDRetraction.envelope.{u} p r n

/-- 有限分冪枠への既存の完備模型の同型。 -/
def crystallineSmallBridgeFrameEquiv :
    pdTerm p (crystallineBase.{u} p) r n ≃ₐ[crystallineBase.{u} p]
      (crystallineSmallBridgeFrameTarget.{u} p r n).carrier :=
  CrystallinePDRetraction.termEquiv.{u} p r n

/-- 小さい結晶の橋の始域を計算する標準の有限 affine 枠。 -/
def crystallineSmallBridgeAffineTerm :=
  affineEnvelopeTerm (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r n
    (polyCutoff (crystallineBasePrism.{u} p) r) le_rfl

/-- 小さい結晶の橋の始域の prism。 -/
def crystallineSmallBridgeSourcePrism : OrientedPrism p (crystallineSmallBridgeAffineTerm.{u} p r n).X.B :=
  (aff.{u} p r ⦋n⦌).X.Q

/-- 小さい結晶の橋の始域の基底脚。 -/
def crystallineSmallBridgeSourceBase : crystallineBase.{u} p →+* (crystallineSmallBridgeAffineTerm.{u} p r n).X.B :=
  (aff.{u} p r ⦋n⦌).X.toHom.toRingHom

/-- 小さい結晶の橋の有限分冪枠における標準の結晶 prism。 -/
def crystallineSmallBridgeFramePrism :
    OrientedPrism p (crystallineSmallBridgeFrameTarget.{u} p r n).carrier :=
  pdEnvelopeCrystalline (crystallineBasePrism.{u} p).deltaStructure
    (residuePdStructure p (crystallineBase_regular p) (CrystallinePDRetraction.local_base p))
    (CrystallinePDRetraction.envelope.{u} p r n) (CrystallinePDRetraction.regular p r n)
    (CrystallinePDRetraction.local_base p) (CrystallinePDRetraction.frobenius_base p)

/-- 結晶基底から有限分冪枠への標準の prism 射。 -/
def crystallineSmallBridgeFrameBase :
    OrientedPrism.Hom (crystallineBasePrism.{u} p) (crystallineSmallBridgeFramePrism.{u} p r n) where
  toRingHom := algebraMap (crystallineBase.{u} p) (crystallineSmallBridgeFrameTarget.{u} p r n).carrier
  map_delta := pdEnvelopeCrystalline_base (crystallineBasePrism.{u} p).deltaStructure
    (residuePdStructure p (crystallineBase_regular p) (CrystallinePDRetraction.local_base p))
    (CrystallinePDRetraction.envelope.{u} p r n) (CrystallinePDRetraction.regular p r n)
    (CrystallinePDRetraction.local_base p) (CrystallinePDRetraction.frobenius_base p)
  ideal_le := by
    change Ideal.span {(crystallineBasePrism.{u} p).generator} ≤ _
    rw [Ideal.span_singleton_le_iff_mem, crystallineBase_generator]
    change algebraMap (crystallineBase.{u} p)
      (crystallineSmallBridgeFrameTarget.{u} p r n).carrier (p : crystallineBase.{u} p) ∈
        Ideal.span {(crystallineSmallBridgeFramePrism.{u} p r n).generator}
    rw [map_natCast]
    change (p : (crystallineSmallBridgeFrameTarget.{u} p r n).carrier) ∈
      Ideal.span {(p : (crystallineSmallBridgeFrameTarget.{u} p r n).carrier)}
    exact Ideal.mem_span_singleton_self _

/-- 既存の小さい結晶の橋を有限分冪枠で読む環射。 -/
def crystallineSmallBridgeFrameMap :
    (crystallineSmallBridgeAffineTerm.{u} p r n).X.B →+*
      (crystallineSmallBridgeFrameTarget.{u} p r n).carrier :=
  (crystallineSmallBridgeFrameEquiv.{u} p r n).toRingHom.comp
    ((crystallineSmallBridge.{u} p r).app ⦋n⦌).hom

/-- 小さい結晶の橋は、始域と有限分冪枠の δ 構造を保つ。 -/
theorem crystallineSmallBridgeFrameMap_isDeltaHom :
    (crystallineSmallBridgeSourcePrism.{u} p r n).deltaStructure.IsDeltaHom
      (crystallineSmallBridgeFramePrism.{u} p r n).deltaStructure
      (crystallineSmallBridgeFrameMap.{u} p r n) := by
  have hb := (bridgeApp_spec.{u} p r ⦋n⦌).1
  rw [crystallineDivisionPrism_deltaStructure] at hb
  have h := (CrystallinePDRetraction.evaluate_delta.{u} p r n).comp hb
  have he : crystallineSmallBridgeFrameMap.{u} p r n =
      (CrystallinePDRetraction.evaluate.{u} p r n).comp (bridgeApp.{u} p r ⦋n⦌) := by
    apply RingHom.ext
    intro x
    change CrystallinePDRetraction.termEquiv.{u} p r n
      ((CrystallinePDRetraction.termEquiv.{u} p r n).symm
        (CrystallinePDRetraction.evaluate.{u} p r n (bridgeApp.{u} p r ⦋n⦌ x))) = _
    exact AlgEquiv.apply_symm_apply _ _
  rw [he]
  exact h

/-- 有限分冪枠への橋は基底の構造射を保つ。 -/
theorem crystallineSmallBridgeFrameMap_base (x : crystallineBase.{u} p) :
    crystallineSmallBridgeFrameMap.{u} p r n (crystallineSmallBridgeSourceBase.{u} p r n x) =
      algebraMap (crystallineBase.{u} p) (crystallineSmallBridgeFrameTarget.{u} p r n).carrier x := by
  have h := ConcreteCategory.congr_hom
    (Under.w ((crystallineSmallBridgeAlgebra.{u} p r).app ⦋n⦌)) x
  change ((crystallineSmallBridge.{u} p r).app ⦋n⦌)
      ((aff.{u} p r ⦋n⦌).X.toHom.toRingHom x) =
    algebraMap (crystallineBase.{u} p) (pdTerm p (crystallineBase.{u} p) r n) x at h
  change crystallineSmallBridgeFrameEquiv.{u} p r n
    (((crystallineSmallBridge.{u} p r).app ⦋n⦌)
      ((aff.{u} p r ⦋n⦌).X.toHom.toRingHom x)) = _
  rw [h]
  exact (crystallineSmallBridgeFrameEquiv.{u} p r n).commutes x

/-- 有限分冪枠への橋は各頂点変数をその p 乗に送る。 -/
theorem crystallineSmallBridgeFrameMap_variable (j : Fin r) (i : Fin (n + 1)) :
    crystallineSmallBridgeFrameMap.{u} p r n
      ((crystallineSmallBridgeAffineTerm.{u} p r n).η
        (affineVariable (crystallineBasePrism.{u} p) r n j i)) =
      (crystallineSmallBridgeFrameTarget.{u} p r n).unit
        (MvPolynomial.X (ULift.up j, i)) ^ p := by
  change crystallineSmallBridgeFrameEquiv.{u} p r n
    (((crystallineSmallBridge.{u} p r).app ⦋n⦌)
      (crystallineSmallSourceVariable.{u} p r n j i)) = _
  rw [crystallineSmallBridge_variable, map_pow]
  apply congrArg (fun x => x ^ p)
  change CrystallinePDRetraction.termEquiv.{u} p r n
    (SerrePositivity.DerivedCompletion.principalCompletionUnitRingHom
      (pdRaw (crystallineBase.{u} p) r n) (p : pdRaw (crystallineBase.{u} p) r n)
      (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i)))) = _
  exact (PDSmallModelComparison.termEquiv_unit p (crystallineBase.{u} p)
    (residuePdStructure p (crystallineBase_regular p) (CrystallinePDRetraction.local_base p))
    (CrystallinePDRetraction.base_prime p) (crystallineBase_complete p)
    (crystallineBase_regular p) r
    (PDPolynomialFunctor.base_ker (J := Ideal.span {(p : crystallineBase.{u} p)})
      (CrystallinePDRetraction.polynomial p r)) n _).trans
    (PDSmallModelComparison.rawToFrame_unit p (crystallineBase.{u} p)
      (residuePdStructure p (crystallineBase_regular p) (CrystallinePDRetraction.local_base p))
      (CrystallinePDRetraction.base_prime p) (crystallineBase_complete p)
      (crystallineBase_regular p) r
      (PDPolynomialFunctor.base_ker (J := Ideal.span {(p : crystallineBase.{u} p)})
        (CrystallinePDRetraction.polynomial p r)) n _)

/-- 有限分冪枠の結晶 prism の選択生成元は p。 -/
theorem crystallineSmallBridgeFramePrism_generator :
    (crystallineSmallBridgeFramePrism.{u} p r n).generator = p := by
  rfl

/-- 有限分冪枠の二頂点の差は分冪イデアルに入る。 -/
theorem crystallineSmallBridgeFrame_difference_mem (j : Fin r) (i : Fin (n + 1)) :
    (crystallineSmallBridgeFrameTarget.{u} p r n).unit (MvPolynomial.X (ULift.up j, i)) -
      (crystallineSmallBridgeFrameTarget.{u} p r n).unit (MvPolynomial.X (ULift.up j, 0)) ∈
        (crystallineSmallBridgeFrameTarget.{u} p r n).ideal := by
  exact CrystallinePDRetraction.difference_mem.{u} p r n j i

/-- 整係数の実際の小さい結晶の橋は、有限 affine 枠の普遍性による橋と一致。 -/
theorem crystallineSmallBridgeFrameMap_eq_affineBridge :
    crystallineSmallBridgeFrameMap.{u} p r n =
      pdEnvelopeAffineBridge (crystallineSmallBridgeBasePD.{u} p) r n
        (crystallineSmallBridgeFrameTarget.{u} p r n)
        (crystallineSmallBridgeFramePrism.{u} p r n)
        (crystallineSmallBridgeFramePrism_generator.{u} p r n)
        (crystallineBasePrism.{u} p) (crystallineSmallBridgeAffineTerm.{u} p r n)
        (crystallineSmallBridgeFrame_difference_mem.{u} p r n)
        (crystallineSmallBridgeFrameBase.{u} p r n) := by
  apply (pdEnvelopeAffineBridge_existsUnique (crystallineSmallBridgeBasePD.{u} p) r n
    (crystallineSmallBridgeFrameTarget.{u} p r n)
    (crystallineSmallBridgeFramePrism.{u} p r n)
    (crystallineSmallBridgeFramePrism_generator.{u} p r n)
    (crystallineBasePrism.{u} p) (crystallineSmallBridgeAffineTerm.{u} p r n)
    (crystallineSmallBridgeFrame_difference_mem.{u} p r n)
    (crystallineSmallBridgeFrameBase.{u} p r n)).choose_spec.2
  refine ⟨crystallineSmallBridgeFrameMap_isDeltaHom.{u} p r n, ?_, ?_⟩
  · apply RingHom.ext
    exact crystallineSmallBridgeFrameMap_base.{u} p r n
  · exact crystallineSmallBridgeFrameMap_variable.{u} p r n

end SerrePositivity.BhattScholze.Prismatic
