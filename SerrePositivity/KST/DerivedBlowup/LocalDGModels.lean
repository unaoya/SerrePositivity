module

public import SerrePositivity.KST.DerivedBlowup.ChartBaseChangeDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ExceptionalConeComparison
public import SerrePositivity.KST.DerivedBlowup.KoszulKFlat

/-!
概要：KST Def3.1・Lemma3.6 と §5.3 のチャート・例外因子・D(n) の局所 dg 模型。
方針：明示した有限関係式列の Koszul 外積一対象 dg 圏を使う。
規約：通常の商環へ置き換えず、全ての Koszul 生成元を次数−1に保持する。
使われ方：導来 blowup の dg チャート図式と局所 perfect 加群。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：例外因子の局所 Koszul dg 圏の対象型。
方針：チャート関係式に Cartier 方程式 a_i を追加する。
規約：KST Lemma3.6。使われ方：E∩U_i の局所 dg 加群圏。 -/
abbrev ExceptionalChartObject (a : Fin (r + 1) → R) (i : Fin (r + 1)) :=
  ExteriorKoszulObject (Finsupp.linearCombination (ChartRing R i) (exceptionalChartSequence a i))

/-- 概要：D(n) の局所 Koszul dg 圏の対象型。
方針：チャート関係式に全ての a_j^n を追加する。
規約：KST §5.3 p.33 の明示式。使われ方：導来 thickening の局所 dg 加群圏。 -/
abbrev ThickeningChartObject (a : Fin (r + 1) → R) (i : Fin (r + 1)) (n : ℕ) :=
  ExteriorKoszulObject (Finsupp.linearCombination (ChartRing R i) (thickeningChartSequence a i n))

/-- 概要：標準チャート dg 圏の Hom 複体は既存の反復 cone Koszul 複体と同型。
方針：有限列の外積比較とチャート添字の比較を使う。
規約：KST Def3.1。使われ方：局所 dg 圏に既存 Koszul 補題を適用する。 -/
def derivedChartDGUnderlyingIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    derivedChartComplex a i ≅
      DifferentialGraded.homObject (ChartRing R i) (DerivedChartObject a i) .point .point :=
  derivedChartExteriorIso a i

/-- 概要：例外因子 dg 圏の Hom 複体は明示した反復 cone Koszul 複体と同型。
方針：一般有限列の外積比較を使う。
規約：KST Lemma3.6。使われ方：例外因子に既存の Koszul API を適用する。 -/
def exceptionalChartDGUnderlyingIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    exceptionalChartComplex a i ≅
      DifferentialGraded.homObject (ChartRing R i) (ExceptionalChartObject a i) .point .point :=
  koszulExteriorIso (exceptionalChartSequence a i)

/-- 概要：D(n) の dg 圏の Hom 複体は明示した反復 cone Koszul 複体と同型。
方針：連結した関係式列の外積比較を使う。
規約：KST §5.3。使われ方：導来 thickening の Koszul ホモロジー。 -/
def thickeningChartDGUnderlyingIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) (n : ℕ) :
    thickeningChartComplex a i n ≅
      DifferentialGraded.homObject (ChartRing R i) (ThickeningChartObject a i n) .point .point :=
  koszulExteriorIso (thickeningChartSequence a i n)

/-- 概要：例外因子の局所 dg 圏の Hom 複体は K-flat。
方針：有限自由生成元の外積 Koszul 複体の K-flat 性を使う。
規約：KST Lemma3.6。使われ方：例外因子の導来スカラー拡大。 -/
theorem exceptionalChartDG_kFlat (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.complexKFlat (ChartRing R i)
      (DifferentialGraded.homObject (ChartRing R i) (ExceptionalChartObject a i) .point .point) :=
  sequenceExteriorCochain_kFlat (exceptionalChartSequence a i)

/-- 概要：D(n) の局所 dg 圏の Hom 複体は K-flat。
方針：連結した有限関係式列に一般 Koszul K-flat 性を使う。
規約：KST §5.3。使われ方：導来 thickening の導来スカラー拡大。 -/
theorem thickeningChartDG_kFlat (a : Fin (r + 1) → R) (i : Fin (r + 1)) (n : ℕ) :
    DifferentialGraded.complexKFlat (ChartRing R i)
      (DifferentialGraded.homObject (ChartRing R i) (ThickeningChartObject a i n) .point .point) :=
  sequenceExteriorCochain_kFlat (thickeningChartSequence a i n)

end SerrePositivity.KST.DerivedBlowup
