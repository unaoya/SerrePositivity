module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.UniversalCrystallineCoefficients
public import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude
public import SerrePositivity.HomologicalAlgebra.RegularQuotientUnboundedModel

/-!
# 特定の結晶被覆の標準係数射の完全 Tor 上界

## 概要
Zp から普遍結晶被覆への既存の射は、任意の有限 Koszul 列について有限完全 Tor 振幅を持つ。

## 方針
係数射の平坦性で通常のホモロジーの下界を保ち、有限 Koszul 列の長さだけ下げる。

## 規約
上界は通常の Tor 振幅ではなく、有限 Koszul 列を含む既存の完全 Tor 振幅である。

## 使われ方
Proposition 6.2 の特定の結晶入力へ Lemma 4.22 を適用する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable (p : ℕ) [Fact p.Prime]

/-- 特定の標準係数射の完全 Tor 上界は、有限 Koszul 列の長さで取れる。 -/
theorem coefficientMap_completeTorAmplitude {r : ℕ} (x : Fin r → crystallineBase.{u} p) :
    HasCochainCompleteTorAmplitude (coefficientMap.{u} p) x r := by
  intro L K q hq hL m hK i hi
  letI : QuasiIso q := hq
  have hLbound : ∀ j : ℤ, j < m → IsZero (L.homology j) := by
    intro j hj
    exact (hK j hj).of_iso (asIso (HomologicalComplex.homologyMap q j))
  exact koszulComplexOn_homology_isZero_below _ m
    (flatBaseChange_homology_isZero_below (coefficientMap.{u} p)
      (coefficientMap_flat.{u} p) L m hLbound) _ i hi

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
