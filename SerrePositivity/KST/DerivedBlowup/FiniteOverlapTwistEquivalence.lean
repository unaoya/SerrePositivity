module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistAction
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeDerivedEvaluation
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraPerfectComparison
public import Mathlib.CategoryTheory.Equivalence

/-!
概要：KST §3.1 の整数捻りを全図式加群圏・主導来圏の自己同値として束ねる。
方針：逆指数の指定自然同型を用い、既存の随伴化構成で同値にする。
規約：局所 perfect 条件は保存・反映する。cartesian 条件の保存は別証明。
使われ方：一般の対象の逆捻りと局所条件の移送。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：指定整数捻りによる全図式加群圏の自己同値。
方針：逆指数の作用を逆関手とし、指定両側逆を随伴化して同値にする。
規約：KST §3.1。使われ方：通常加群の逆捻りと Hom 比較。 -/
def finiteOverlapTwistEquivalence (m : ℤ) :
    AllDiagramModules (finiteOverlapDGAlgebraDiagram R a) ≌
      AllDiagramModules (finiteOverlapDGAlgebraDiagram R a) :=
  CategoryTheory.Equivalence.mk (finiteOverlapTwistAction R a m) (finiteOverlapTwistAction R a (-m))
    (by simpa only [neg_neg] using (finiteOverlapTwistActionInverseIso R a (-m)).symm)
    (finiteOverlapTwistActionInverseIso R a m)

/-- 概要：指定通常加群の自己同値の順関手は元の捻り作用。
方針：随伴化は関手を変えない。
規約：KST §3.1。使われ方：自己同値と指定作用の接続。 -/
theorem finiteOverlapTwistEquivalence_functor (m : ℤ) :
    (finiteOverlapTwistEquivalence R a m).functor = finiteOverlapTwistAction R a m := rfl

/-- 概要：指定整数捻りによる全図式主導来圏の自己同値。
方針：逆指数の導来作用を逆関手とし、指定両側逆を随伴化する。
規約：KST §3.1。使われ方：導来対象の逆捻りと Hom 比較。 -/
def finiteOverlapDerivedTwistEquivalence (m : ℤ) :
    DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a) ≌
      DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a) :=
  CategoryTheory.Equivalence.mk (finiteOverlapDerivedTwistAction R a m)
    (finiteOverlapDerivedTwistAction R a (-m))
    (by simpa only [neg_neg] using (finiteOverlapDerivedTwistActionInverseIso R a (-m)).symm)
    (finiteOverlapDerivedTwistActionInverseIso R a m)

/-- 概要：指定導来自己同値の順関手は元の導来捻り作用。
方針：随伴化の定義を読む。
規約：KST §3.1。使われ方：自己同値と指定導来作用の接続。 -/
theorem finiteOverlapDerivedTwistEquivalence_functor (m : ℤ) :
    (finiteOverlapDerivedTwistEquivalence R a m).functor =
      finiteOverlapDerivedTwistAction R a m := rfl

/-- 概要：全整数の捻り作用は正規表示での任意対象の局所 perfect 性を保存・反映する。
方針：一般の gauge 制限の局所導来評価同型を具体的な捻りへ適用する。
規約：KST §3.1。使われ方：大域 Perf 条件の局所部分。 -/
theorem finiteOverlapDerivedTwistAction_algebraLocallyPerfect_iff (m : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramAlgebraLocallyPerfect (finiteOverlapDGAlgebraDiagram R a)
        ((finiteOverlapDerivedTwistAction R a m).obj X) ↔
      diagramAlgebraLocallyPerfect (finiteOverlapDGAlgebraDiagram R a) X :=
  diagramGaugeDerivedAction_locallyPerfect_iff (finiteOverlapDGAlgebraDiagram R a)
    (finiteOverlapTwistGauge R a m) X

/-- 概要：全整数の捻りは元の Koszul 表示でも任意対象の局所 perfect 性を保存・反映。
方針：正規表示との局所 perfect 条件の同値を両側に適用する。
規約：KST §3.1、cartesian 条件は別義務。
使われ方：元の有限重なり模型での一般対象の捻り。 -/
theorem finiteOverlapDerivedTwistAction_locallyPerfect_iff (m : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramLocallyPerfect R a ((finiteOverlapDerivedTwistAction R a m).obj X) ↔
      diagramLocallyPerfect R a X :=
  (finiteOverlapAlgebraLocallyPerfect_iff R a _).symm.trans
    ((finiteOverlapDerivedTwistAction_algebraLocallyPerfect_iff R a m X).trans
      (finiteOverlapAlgebraLocallyPerfect_iff R a X))

end SerrePositivity.KST.DerivedBlowup
