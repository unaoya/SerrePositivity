module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineSmallBridgeModP
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDInclusion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 小さい結晶の橋の頂点座標

## 概要
小さい分冪模型への結晶の橋は、有限枠の各頂点変数を p 乗へ送る。

## 方針
結晶評価の δ 両立と、小さい模型の変数の δ が零であることを使う。

## 規約
余単体の次数を自然数で指定し、既存の affine 包の構造脚上で式を述べる。

## 使われ方
BS 著者版 Theorem 6.4 の Witt の指定された比較射との照合。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "k" => crystallineBase p
local notation "Z" => crystallineBasePrism p
local notation "γ" => residuePdStructure p (crystallineBase_regular p) (local_base p)
local notation "E" n => envelope p r n
local notation "Qp" n => pdEnvelopeCrystalline (OrientedPrism.deltaStructure Z) γ (E n)
  (regular p r n) (local_base p) (frobenius_base p)
local notation "D" n => completedFreeDeltaStructure Z (AffineIndex r n)

private theorem evaluate_frobenius_variable (n : ℕ) (j : Fin r) (i : Fin (n + 1)) :
    evaluate.{u} p r n (pdDeltaUnit.{u} p r ⦋n⦌
      ((D n).frobeniusLift (affineVariable Z r n j i))) =
      evaluate.{u} p r n (pdDeltaUnit.{u} p r ⦋n⦌ (affineVariable Z r n j i)) ^ p := by
  have h₁ := (pdDeltaUnit_isDeltaHom.{u} p r ⦋n⦌).map_frobeniusLift
    (affineVariable Z r n j i)
  have h₂ := (evaluate_delta.{u} p r n).map_frobeniusLift
    (pdDeltaUnit.{u} p r ⦋n⦌ (affineVariable Z r n j i))
  have h := (congrArg (evaluate.{u} p r n) h₁).trans h₂
  have hx := evaluate_variable.{u} p r n j i
  calc
    _ = (Qp n).deltaStructure.frobeniusLift
        (evaluate.{u} p r n (pdDeltaUnit.{u} p r ⦋n⦌ (affineVariable Z r n j i))) := h
    _ = (Qp n).deltaStructure.frobeniusLift
        ((E n).unit (MvPolynomial.X (ULift.up j, i))) := congrArg _ hx
    _ = ((E n).unit (MvPolynomial.X (ULift.up j, i))) ^ p := by
      rw [DeltaStructure.frobeniusLift_apply, pdEnvelopeCrystalline_delta_X, mul_zero, add_zero]
    _ = _ := congrArg (fun x => x ^ p) hx.symm

/-- 結晶基底の affine 包における、指定された頂点の変数。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.crystallineSmallSourceVariable
    (n : ℕ) (j : Fin r) (i : Fin (n + 1)) : (zpCech.{u} p r).obj ⦋n⦌ := by
  exact (aff.{u} p r ⦋n⦌).η (affineVariable Z r n j i)

/-- 小さい完備分冪模型における、指定された頂点の変数。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.crystallineSmallTargetVariable
    (n : ℕ) (j : Fin r) (i : Fin (n + 1)) : (pdRings.{u} p r).obj ⦋n⦌ := by
  exact SerrePositivity.DerivedCompletion.principalCompletionRingCatUnit p
    (CommRingCat.of (pdRaw (crystallineBase.{u} p) r n))
      (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i)))

/-- 小さい結晶の橋は各頂点変数を、対応する分冪模型の変数の p 乗に送る。 -/
theorem _root_.SerrePositivity.BhattScholze.Prismatic.crystallineSmallBridge_variable
    (n : ℕ) (j : Fin r) (i : Fin (n + 1)) :
    (crystallineSmallBridge.{u} p r).app ⦋n⦌ (crystallineSmallSourceVariable.{u} p r n j i) =
      crystallineSmallTargetVariable.{u} p r n j i ^ p := by
  let e := termEquiv.{u} p r n
  apply e.injective
  change e (e.symm (evaluate.{u} p r n
    (bridgeApp.{u} p r ⦋n⦌ ((aff.{u} p r ⦋n⦌).η (affineVariable Z r n j i))))) = _
  rw [AlgEquiv.apply_symm_apply]
  have hb := RingHom.congr_fun (bridgeApp_spec.{u} p r ⦋n⦌).2
    (affineVariable Z r n j i)
  change bridgeApp.{u} p r ⦋n⦌ ((aff.{u} p r ⦋n⦌).η (affineVariable Z r n j i)) =
    pdDeltaUnit.{u} p r ⦋n⦌ ((D n).frobeniusLift (affineVariable Z r n j i)) at hb
  rw [hb, evaluate_frobenius_variable, map_pow]
  apply congrArg (fun x => x ^ p)
  have h := congrArg e (at_variable.{u} p r n j i)
  change e (e.symm (evaluate.{u} p r n
    (pdDeltaUnit.{u} p r ⦋n⦌ (affineVariable Z r n j i)))) = _ at h
  simpa only [AlgEquiv.apply_symm_apply, crystallineSmallTargetVariable] using h

end SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction
