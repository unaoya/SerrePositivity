module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineHodgeTateSquare
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.UniversalCrystallineCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCartierAssembly

/-!
# 普遍向き付き prism の特定の結晶被覆での標準 HT 同型

## 概要
元の Zp の標準 HT 同型を、普遍向き付き prism の Construction 6.1 の被覆へ運ぶ。

## 方針
元の係数射の平坦性と、同じ標準 HT 写像の係数正方形を使う。

## 規約
一般の結晶 HT 比較を入力にせず、Zp の既存の計算だけを入力に使う。

## 使われ方
BS Proposition 6.2 で普遍向き付き基底へ降下するための、特定の被覆での入力。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable (p : ℕ) [Fact p.Prime]

/-- 元の普遍向き付き prism の特定の結晶被覆上で、全次数の元の標準 HT 写像は同型。 -/
theorem universalCrystallineCover_hodgeTate_iso (r : ℕ) :
    HodgeTateIsoStatement
      (Construction61.crystallineCover (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
      (Construction61.crystallineCover_bounded (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) r :=
  affineCrystallineRawHT_transfer (coefficientHom.{u} p)
    (crystallineBaseBounded.{u} p)
    (Construction61.crystallineCover_bounded (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    (crystallineBase_generator.{u} p)
    (Construction61.crystallineCover_generator (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    (coefficientMap_flat.{u} p) r (hodgeTate_of_deRham_cartier.{u} p r)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
