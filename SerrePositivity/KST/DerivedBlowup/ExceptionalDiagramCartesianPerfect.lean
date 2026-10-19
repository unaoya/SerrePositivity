module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientCartesianPerfect
public import SerrePositivity.KST.DerivedBlowup.ExceptionalDiagramDerivedComparison

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子と共通 Koszul 表示の大域候補比較。
方針：実際の指定係数図式同型へ cartesian perfect 条件の表示不変性を適用する。
規約：canonical な比較の可逆性を用いる図式模型。層の降下比較は別義務。
使われ方：例外因子の半直交分解に向けた Perf 候補の共通表示。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory
variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：例外因子の指定導来制限は cartesian perfect 条件を保存・反映する。
方針：実際の有限重なり係数図式同型に一般の iff を適用する。
規約：KST Lemma 3.6、共通 Koszul 表示による再構成。
使われ方：元の例外因子の大域候補を共通表示で判定する。 -/
theorem exceptionalDiagramDerivedRestriction_cartesianPerfect_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalProductDiagram R a)) :
    diagramAlgebraCartesianPerfect (finiteOverlapExceptionalDGAlgebraDiagram R a)
        ((exceptionalDiagramDerivedEquivalence R a).inverse.obj X) ↔
      diagramAlgebraCartesianPerfect (finiteOverlapExceptionalProductDiagram R a) X :=
  diagramCoefficientDerivedRestriction_cartesianPerfect_iff (R := R)
    (finiteOverlapExceptionalProductDiagramIso R a) X

/-- 概要：例外因子の元の表示と共通 Koszul 表示の cartesian perfect 導来部分圏の同値。
方針：指定延長–制限同値を保存・反映する二条件で制限する。
規約：KST Lemma 3.6、層の Perf との比較は別に残す。
使われ方：半直交分解で用いる例外因子の大域図式候補の表示変更。 -/
def exceptionalDiagramCartesianPerfectEquivalence (a : I → R) :
    (diagramAlgebraCartesianPerfect
      (finiteOverlapExceptionalDGAlgebraDiagram R a)).FullSubcategory ≌
    (diagramAlgebraCartesianPerfect
      (finiteOverlapExceptionalProductDiagram R a)).FullSubcategory :=
  diagramCoefficientCartesianPerfectEquivalence (R := R)
    (finiteOverlapExceptionalProductDiagramIso R a)

end SerrePositivity.KST.DerivedBlowup
