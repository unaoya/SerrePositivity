module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientDerivedEquivalence
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalProductDiagram

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子と共通 Koszul 表示の全図式加群の導来比較。
方針：指定係数図式同型から係数 dg 準同値を作り、指定導来延長–制限同値を適用する。
規約：全図式加群の比較。cartesian・局所 perfect 条件と層の降下は別に残す。
使われ方：例外因子の dg 加群模型の表示比較の基礎。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：元の例外因子係数図式を持つ図式加群の係数 dg 圏の対象型。
方針：既存の一般の係数圏を実際の例外因子図式へ適用する。
規約：KST Lemma 3.6。使われ方：元の例外因子の図式 dg 加群の係数。 -/
abbrev ExceptionalDiagramCoefficientObject (a : I → R) :=
  DiagramModuleCoefficientObject (finiteOverlapExceptionalDGAlgebraDiagram R a)

/-- 概要：共通 Ko(A;a) 表示の図式加群の係数 dg 圏の対象型。
方針：同じ有限重なりの添字を持つ共通表示図式を使う。
規約：KST Lemma 3.6。使われ方：共通表示の図式 dg 加群の係数。 -/
abbrev ExceptionalProductDiagramCoefficientObject (a : I → R) :=
  DiagramModuleCoefficientObject (finiteOverlapExceptionalProductDiagram R a)

/-- 概要：例外因子の指定図式比較が誘導する係数 dg 関手。
方針：各 Hom に行先の指定 Koszul 同型を適用する一般構成を使う。
規約：KST Lemma 3.6、元の添字を保持する。
使われ方：実際の dg 図式加群の制限・係数拡大。 -/
def exceptionalDiagramCoefficientDGFunctor (a : I → R) :
    DGFunctor R (ExceptionalDiagramCoefficientObject R a)
      (ExceptionalProductDiagramCoefficientObject R a) :=
  diagramCoefficientDGFunctor (finiteOverlapExceptionalProductDiagramIso R a).hom

/-- 概要：例外因子の係数 dg 比較は準同値。
方針：指定図式同型に対する一般の Hom 同型性と本質的全射性を使う。
規約：KST Lemma 3.6。使われ方：全図式加群の導来比較への入力。 -/
theorem exceptionalDiagramCoefficientDGFunctor_quasiEquivalence (a : I → R) :
    QuasiEquivalence (exceptionalDiagramCoefficientDGFunctor R a) :=
  diagramCoefficientDGFunctor_quasiEquivalence (finiteOverlapExceptionalProductDiagramIso R a)

/-- 概要：例外因子の元の表示と共通 Koszul 表示の全図式加群の指定導来同値。
方針：指定係数図式同型から構成した導来延長–制限同値を使う。
規約：KST Lemma 3.6、cartesian perfect 模型への制限と層比較はまだ主張しない。
使われ方：例外因子の大域 dg 加群模型の表示比較。 -/
def exceptionalDiagramDerivedEquivalence (a : I → R) :
    DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a) ≌
      DerivedAllDiagramModules (finiteOverlapExceptionalProductDiagram R a) :=
  diagramCoefficientDerivedEquivalence (R := R) (finiteOverlapExceptionalProductDiagramIso R a)

/-- 概要：例外因子の表示比較の逆関手は指定係数 dg 関手に沿う導来制限。
方針：一般の指定導来同値の逆関手の定義を読む。
規約：KST Lemma 3.6。使われ方：局所評価・cartesian 条件との比較。 -/
theorem exceptionalDiagramDerivedEquivalence_inverse (a : I → R) :
    (exceptionalDiagramDerivedEquivalence R a).inverse =
      dgDerivedRestriction R (ExceptionalDiagramCoefficientObject R a)ᵒᵖ
        (ExceptionalProductDiagramCoefficientObject R a)ᵒᵖ
        (exceptionalDiagramCoefficientDGFunctor R a).op := rfl

end SerrePositivity.KST.DerivedBlowup
