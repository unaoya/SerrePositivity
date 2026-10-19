module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalDiagramCartesianEnhancement
public import SerrePositivity.KST.DerivedBlowup.ExceptionalDiagramCartesianPerfect

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の元の例外因子 dg 候補と共通 Koszul 表示の H⁰ 比較。
方針：元の局所表示の対象条件を正規表示へ移し、指定係数図式同値と合成する。
規約：図式加群模型での再構成。層の Perf・高次降下との同値は別義務。
使われ方：例外因子の共通 Ko(A;a) 表示を大域の dg 候補の H⁰ で使用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：元の例外因子 dg 候補の H⁰ と正規表示の cartesian perfect 部分圏の同値。
方針：canonical な対象条件の等号で指定 H⁰ 比較の行先を移す。
規約：KST §3.1・Lemma 3.6。使われ方：既存の指定係数図式比較への接続。 -/
def exceptionalCartesianPerfectDiagramNormalizedEquivalence (a : I → R) :
    HomotopyCategory R (ExceptionalCartesianPerfectDiagramDGModel R a) ≌
      (diagramAlgebraCartesianPerfect
        (finiteOverlapExceptionalDGAlgebraDiagram R a)).FullSubcategory := by
  rw [finiteOverlapExceptionalAlgebraCartesianPerfect_eq]
  exact exceptionalCartesianPerfectDiagramHomotopyEquivalence R a

/-- 概要：元の例外因子 dg 候補の H⁰ と共通 Koszul 表示の指定導来部分圏の同値。
方針：指定 H⁰ 比較と対象条件を保存・反映する指定係数図式同値を合成する。
規約：KST v4 Lemma 3.6（pp.11–14）、図式加群による再構成。
使われ方：半直交分解に向けた元の dg 候補と共通 Ko(A;a) 表示の接続。 -/
def exceptionalCartesianPerfectDiagramProductEquivalence (a : I → R) :
    HomotopyCategory R (ExceptionalCartesianPerfectDiagramDGModel R a) ≌
      (diagramAlgebraCartesianPerfect
        (finiteOverlapExceptionalProductDiagram R a)).FullSubcategory :=
  (exceptionalCartesianPerfectDiagramNormalizedEquivalence R a).trans
    (exceptionalDiagramCartesianPerfectEquivalence R a)

end SerrePositivity.KST.DerivedBlowup
