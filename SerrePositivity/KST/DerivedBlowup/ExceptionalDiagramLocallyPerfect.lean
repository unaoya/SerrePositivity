module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientLocallyPerfect
public import SerrePositivity.KST.DerivedBlowup.ExceptionalDiagramDerivedComparison

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の導来表示比較を局所 perfect 条件へ制限する。
方針：実際の指定係数図式同型に一般の局所評価比較と perfect 判定を適用する。
規約：正規表示の局所 perfect 導来図式加群。cartesian 性と層比較は別に残す。
使われ方：例外因子の大域 Perf 候補を二つの表示で扱うための局所有限性。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：例外因子の指定導来制限は全対象の局所 perfect 性を保存・反映する。
方針：実際の共通 Koszul 表示との図式同型に一般の perfect 判定を適用する。
規約：KST Lemma 3.6、指定局所評価を使う。
使われ方：例外因子の表示比較を局所 perfect 部分圏へ制限する。 -/
theorem exceptionalDiagramDerivedRestriction_locallyPerfect_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalProductDiagram R a)) :
    diagramAlgebraLocallyPerfect (finiteOverlapExceptionalDGAlgebraDiagram R a)
        ((exceptionalDiagramDerivedEquivalence R a).inverse.obj X) ↔
      diagramAlgebraLocallyPerfect (finiteOverlapExceptionalProductDiagram R a) X :=
  diagramCoefficientDerivedRestriction_locallyPerfect_iff (R := R)
    (finiteOverlapExceptionalProductDiagramIso R a) X

/-- 概要：例外因子の元の表示と共通 Koszul 表示の局所 perfect 導来部分圏の指定同値。
方針：元の指定延長–制限同値を、保存・反映する局所条件で制限する。
規約：KST Lemma 3.6、cartesian 条件の比較は引き続き必要。
使われ方：例外因子の二つの大域 dg 加群模型の局所有限性の同定。 -/
def exceptionalDiagramLocallyPerfectEquivalence (a : I → R) :
    (diagramAlgebraLocallyPerfect (finiteOverlapExceptionalDGAlgebraDiagram R a)).FullSubcategory ≌
      (diagramAlgebraLocallyPerfect (finiteOverlapExceptionalProductDiagram R a)).FullSubcategory :=
  diagramCoefficientLocallyPerfectEquivalence (R := R)
    (finiteOverlapExceptionalProductDiagramIso R a)

end SerrePositivity.KST.DerivedBlowup
