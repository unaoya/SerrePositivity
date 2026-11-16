module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCompletedTotals
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.UniversalCrystallineAmplitude

/-!
# 特定の普遍結晶被覆への元の affine 完備導来 Tot 比較

## 概要
標準 Zp 係数射に沿う元の affine 完備導来 Tot 比較が同型になることを示す。

## 方針
元の係数射の平坦性と長さ一の完全 Tor 上界を、元の affine 模型へ接続した比較に渡す。

## 規約
一般の結晶 Hodge–Tate 比較は仮定しない。この同型だけで標準 HT 写像の全単射性とはしない。

## 使われ方
Proposition 6.2 の特定の結晶入力へ、Zp の既存の標準 HT 計算を移す比較。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable (p : ℕ) [Fact p.Prime]

/-- 特定の標準 Zp 射に沿う、元の affine 模型の標準完備導来 Tot 比較。 -/
def universalCrystallineAffineTotalComparison (r : ℕ) :=
  affineCrystallineCompletedTotalComparison (coefficientHom.{u} p)
    (crystallineBaseBounded.{u} p)
    (Construction61.crystallineCover_bounded
      (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    (crystallineBase_generator.{u} p)
    (Construction61.crystallineCover_generator
      (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    (coefficientMap_flat.{u} p) r

/-- 元の特定の標準 Zp 射の affine 完備導来 Tot 比較は同型である。 -/
theorem universalCrystallineAffineTotalComparison_isIso (r : ℕ) :
    IsIso (universalCrystallineAffineTotalComparison.{u} p r) :=
  affineCrystallineCompletedTotalComparison_isIso (coefficientHom.{u} p)
    (crystallineBaseBounded.{u} p)
    (Construction61.crystallineCover_bounded
      (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    (crystallineBase_generator.{u} p)
    (Construction61.crystallineCover_generator
      (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    (coefficientMap_flat.{u} p) r 1
    (coefficientMap_completeTorAmplitude.{u} p _)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
