module

public import SerrePositivity.KST.DerivedBlowup.LocalDGModels
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat

/-!
概要：KST Def3.1・Lemma3.6 と §5.3 の局所 dg 模型は Hom ごとに K-flat。
方針：一対象 Koszul dg 圏の全 Hom が同じ有限 Koszul 外積複体であることを使う。
規約：非有界 acyclic 試験複体を使う既存 localHomKFlat。
使われ方：導来 dg スカラー拡大と局所 perfect 加群の比較。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：標準チャート dg 圏は localHomKFlat を満たす。
方針：チャートの underlying Koszul 同型から K-flat 性を移す。
規約：KST Def3.1。使われ方：チャートの導来係数変更。 -/
theorem derivedChart_localHomKFlat (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.localHomKFlat (ChartRing R i) (DerivedChartObject a i) := by
  intro x y
  exact DifferentialGraded.complexKFlat_of_iso (ChartRing R i)
    (derivedChartDGUnderlyingIso a i).symm (derivedChartComplex_kFlat a i)

/-- 概要：例外因子の局所 dg 圏は localHomKFlat を満たす。
方針：全 Hom は同じ有限列の外積 Koszul 複体。
規約：KST Lemma3.6。使われ方：例外因子の導来係数変更。 -/
theorem exceptionalChart_localHomKFlat (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.localHomKFlat (ChartRing R i) (ExceptionalChartObject a i) := by
  intro x y
  exact exceptionalChartDG_kFlat a i

/-- 概要：D(n) の局所 dg 圏は localHomKFlat を満たす。
方針：全 Hom は連結した関係式列の外積 Koszul 複体。
規約：KST §5.3。使われ方：導来 thickening の導来係数変更。 -/
theorem thickeningChart_localHomKFlat (a : Fin (r + 1) → R) (i : Fin (r + 1)) (n : ℕ) :
    DifferentialGraded.localHomKFlat (ChartRing R i) (ThickeningChartObject a i n) := by
  intro x y
  exact thickeningChartDG_kFlat a i n

end SerrePositivity.KST.DerivedBlowup
