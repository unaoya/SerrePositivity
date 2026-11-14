module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineSmallBridgeModP
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetractionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineSmallBridgeModP
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 小さい分冪模型への整係数の結晶の橋

## 概要
Frobenius の橋に分冪評価を続けた厳密な余単体射を固定する。

## 方針
既存の橋と評価を合成し、生成元の像を使って実際の mod p の射を照合する。

## 規約
基底は既存の結晶基底 ℤ_p。小さい模型の頂点変数の δ は零。

## 使われ方
BS 著者版 Theorem 6.4 の Witt の比較への底変換。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

/-- 整係数の結晶の橋を小さい分冪模型へ送る。 -/
def crystallineSmallBridge : zpCech.{u} p r ⟶ pdRings.{u} p r :=
  crystallineBridge.{u} p r ≫ crystallineSmallRetraction.{u} p r

/-- 小さい結晶の橋は prism の生成元を p に送る。 -/
theorem crystallineSmallBridge_generator (n : SimplexCategory) :
    (crystallineSmallBridge.{u} p r).app n
      (htGenerator (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r n) =
      (p : (pdRings.{u} p r).obj n) := by
  change (crystallineSmallRetraction.{u} p r).app n
    ((crystallineBridge.{u} p r).app n (htGenerator _ _ r n)) = _
  rw [crystallineBridge_generator]
  exact map_natCast ((crystallineSmallRetraction.{u} p r).app n).hom p

/-- mod p の小さい橋は整係数の厳密な比較射の還元である。 -/
theorem crystallineSmallBridgeModP_eq_reduction :
    crystallineSmallBridgeModP.{u} p r =
      quotPowMap (zpCech.{u} p r) (htGenerator _ _ r) (htGenerator_nat _ _ r)
        (fun n => (p : (pdRings.{u} p r).obj n))
        (fun θ => map_natCast ((pdRings.{u} p r).map θ).hom p)
        (crystallineSmallBridge.{u} p r) (crystallineSmallBridge_generator p r) 1 := by
  apply NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end SerrePositivity.BhattScholze.Prismatic
