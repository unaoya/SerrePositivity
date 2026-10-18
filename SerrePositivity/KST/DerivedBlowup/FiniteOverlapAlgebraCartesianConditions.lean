module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraCartesianComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition
public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianEnhancement

/-!
概要：KST §3.1 の全有限重なりでの cartesian・局所 perfect 条件の表示不変性。
方針：各包含の指定比較の可逆性の iff と各頂点の perfect 条件の iff を束ねる。
規約：同じ全図式導来加群に対する二つの条件を比較する。
使われ方：既存の大域 dg 模型の対象を正規表示で検証する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：全包含での正規表示の cartesian 条件は元の Koszul 模型の条件と一致する。
方針：各包含で証明した可逆性の iff を全称化する。
規約：KST §3.1。使われ方：既存の大域 cartesian 部分圏との接続。 -/
theorem finiteOverlapAlgebraCartesian_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramAlgebraCartesian (finiteOverlapDGAlgebraDiagram R a) X ↔ diagramCartesian R a X :=
  forall_congr' (fun T => forall_congr' (fun U => forall_congr' (fun h =>
    (finiteOverlapAlgebraDerivedExtensionComparison_isIso_iff R a (T := T) (U := U) h X).symm)))

/-- 概要：正規表示での cartesian・局所 perfect 条件は既存の Perf 候補の条件と一致する。
方針：二つの構成済み iff の論理積を取る。
規約：KST §3.1。使われ方：既存の射影的 dg 模型の対象条件を保持する。 -/
theorem finiteOverlapAlgebraCartesianPerfect_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramAlgebraCartesianPerfect (finiteOverlapDGAlgebraDiagram R a) X ↔
      diagramCartesianPerfect R a X :=
  and_congr (finiteOverlapAlgebraCartesian_iff R a X)
    (finiteOverlapAlgebraLocallyPerfect_iff R a X)

/-- 概要：正規表示の cartesian perfect 条件は既存の対象性質そのものと等しい。
方針：全対象での構成済み iff に関数外延性と命題外延性を使う。
規約：KST §3.1。使われ方：既存の充満部分圏の比較の移送。 -/
theorem finiteOverlapAlgebraCartesianPerfect_eq (a : I → R) :
    diagramAlgebraCartesianPerfect (finiteOverlapDGAlgebraDiagram R a) =
      diagramCartesianPerfect R a :=
  funext (fun X => propext (finiteOverlapAlgebraCartesianPerfect_iff R a X))

/-- 概要：既存の射影的 dg 候補の H⁰ は正規表示の cartesian perfect 部分圏と同値。
方針：対象条件の証明済みの等号に沿って既存の H⁰ 比較を移す。
規約：KST §3.1、層・dg 商・高次降下との比較は別の証明義務。
使われ方：正規表示で検証した整合性を同じ大域 dg 候補で利用する。 -/
def finiteOverlapAlgebraCartesianPerfectHomotopyEquivalence (a : I → R) :
    HomotopyCategory R (CartesianPerfectDiagramDGModel R a) ≌
      (diagramAlgebraCartesianPerfect (finiteOverlapDGAlgebraDiagram R a)).FullSubcategory := by
  rw [finiteOverlapAlgebraCartesianPerfect_eq]
  exact cartesianPerfectDiagramHomotopyEquivalence R a

end SerrePositivity.KST.DerivedBlowup
