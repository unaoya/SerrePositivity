module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.UniversalCrystallineAmplitude
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 特定の普遍結晶被覆への標準完備底変換と Tot

## 概要
標準 Zp 係数射について、元の導来係数拡大と p 完備化の自然な Tot 比較が同型である。

## 方針
p 正則性から得た平坦性と長さ一の完全 Tor 上界を、検証済みの Lemma 4.22 に渡す。

## 規約
行の一様なホモロジー下界を要求する。入力の K-flat 性は要求しない。

## 使われ方
Proposition 6.2 の特定の結晶入力の Tot 比較。HT 写像の同型性自体はこの補題の結論ではない。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open HTComparisonTotal
variable (p : ℕ) [Fact p.Prime]

/-- 特定の結晶係数射の元の p 完備導来底変換–Tot 比較は同型である。 -/
theorem coefficientMap_completedTotalComparison_isIso
    (X : CosimplicialObject (Complex (crystallineBase.{u} p))) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    IsIso (cosimplicialNativeCompletedBaseChangeComparison (coefficientMap.{u} p)
      (fun _ : Fin 1 => (p : crystallineBase.{u} p)) X b hX) :=
  cosimplicialNativeCompletedBaseChangeComparison_isIso (coefficientMap.{u} p)
    (fun _ : Fin 1 => (p : crystallineBase.{u} p)) 1
    (coefficientMap_completeTorAmplitude.{u} p _) X b hX

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
