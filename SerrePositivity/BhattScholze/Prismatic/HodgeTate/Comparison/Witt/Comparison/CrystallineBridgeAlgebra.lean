module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineSmallBridgeModP
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction

/-!
# 結晶の橋の基底線形性

## 概要
既存の整係数の結晶の橋を ℤ_p 上の厳密な余単体的代数射として読む。

## 方針
基底上の Frobenius が恒等射であることを、affine 包の標準脚上の式に適用する。

## 規約
台環の射は既存の結晶の橋を使う。

## 使われ方
BS 著者版 Theorem 6.4 の複体と導来底変換への適用。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p

private theorem crystallineBridge_base (n : ℕ) (c : crystallineBase.{u} p) :
    bridgeApp.{u} p r ⦋n⦌ ((aff.{u} p r ⦋n⦌).X.toHom.toRingHom c) =
      pdDeltaUnit.{u} p r ⦋n⦌ (completedFreeDeltaBase Z (AffineIndex r n) c) := by
  rw [← RingHom.congr_fun (aff.{u} p r ⦋n⦌).base_eq c]
  have h := RingHom.congr_fun (bridgeApp_spec.{u} p r ⦋n⦌).2
    (completedFreeDeltaBase Z (AffineIndex r n) c)
  change bridgeApp.{u} p r ⦋n⦌
    ((aff.{u} p r ⦋n⦌).η (completedFreeDeltaBase Z (AffineIndex r n) c)) =
      pdDeltaUnit.{u} p r ⦋n⦌
        ((completedFreeDeltaStructure Z (AffineIndex r n)).frobeniusLift
          (completedFreeDeltaBase Z (AffineIndex r n) c)) at h
  have hb := (completedFreeDeltaBase_isDeltaHom Z (AffineIndex r n)).map_frobeniusLift c
  have hfrob : (Z).deltaStructure.frobeniusLift c = c := by
    change (crystallineBaseDelta p).frobeniusLift c = c
    rw [crystallineBaseDelta_frobenius, RingHom.id_apply]
  rw [← hb, hfrob] at h
  exact h

/-- 結晶の Frobenius の橋を、基底上の厳密な代数射として読む。 -/
def crystallineBridgeAlgebra :
    polyCosimplicialAlgebra (crystallineBasePrism.{u} p) hZ r ⟶ pdDeltaModel.{u} p r where
  app n := by
    obtain ⟨n⟩ := n
    refine Under.homMk (CommRingCat.ofHom
      (R := (zpCech.{u} p r).obj ⦋n⦌)
      (S := (pdDeltaRings.{u} p r).obj ⦋n⦌) (bridgeApp.{u} p r ⦋n⦌)) ?_
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact crystallineBridge_base.{u} p r n c
  naturality {m n} θ := by
    obtain ⟨m⟩ := m
    obtain ⟨n⟩ := n
    apply Under.UnderMorphism.ext
    exact (crystallineBridge.{u} p r).naturality θ

/-- 小さい分冪模型への整係数の結晶の橋の基底線形な形。 -/
def crystallineSmallBridgeAlgebra :
    polyCosimplicialAlgebra (crystallineBasePrism.{u} p) hZ r ⟶
      pdModel p (crystallineBase.{u} p) r :=
  crystallineBridgeAlgebra.{u} p r ≫ CrystallinePDRetraction.retraction.{u} p r

/-- 基底を忘れると、指定された整係数の小さい結晶の橋になる。 -/
theorem crystallineSmallBridgeAlgebra_forget :
    Functor.whiskerRight (crystallineSmallBridgeAlgebra.{u} p r)
      (Under.forget (CommRingCat.of (crystallineBase.{u} p))) =
      crystallineSmallBridge.{u} p r := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  rfl

end SerrePositivity.BhattScholze.Prismatic
