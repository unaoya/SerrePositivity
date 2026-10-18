module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraModuleComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation

/-!
概要：KST §3.1 の指定導来制限比較の正規表示との一致。
方針：実加群の主局所化像で指定制限を計算し、加群段階の一致を送る。
規約：同じ大域導来図式加群に対する canonical な射を比較する。
使われ方：局所 dg 表示に依存しない cartesian 条件の証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 正規表示と元の二つの局所化環の主導来局所化の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の dg 加群圏を照合するために必要。
/-- 概要：実加群上の指定導来制限比較は正規表示への制限と整合する。
方針：両比較を指定加群比較の局所化像として計算する。
規約：KST §3.1。使われ方：canonical な導来比較の表示比較。 -/
theorem finiteOverlapAlgebraDerivedRestrictionComparison_Q (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (dgDerivedRestriction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a T)ᵒᵖ (finiteOverlapAlgebraVertexToChart R a T).op).map
        ((finiteOverlapDerivedRestrictionNatTrans R a h).app
          ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M)) =
      (diagramAlgebraDerivedRestrictionNatTrans (finiteOverlapDGAlgebraDiagram R a) h).app
        ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M) := by
  rw [finiteOverlapDerivedRestrictionNatTrans_app_Q_map,
    diagramAlgebraDerivedRestrictionNatTrans_app_Q_map,
    transitionDerivedRestriction_map_Q, finiteOverlapAlgebraModuleComparison]

set_option maxHeartbeats 2000000 in
-- 正規表示と元の局所導来制限の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の dg 加群圏を照合するために必要。
/-- 概要：全導来対象で指定導来制限比較は正規表示への制限と整合する。
方針：主局所化の対象が保持する実加群に計算公式を適用する。
規約：KST §3.1。使われ方：二つの表示の随伴比較の同定。 -/
theorem finiteOverlapAlgebraDerivedRestrictionComparison (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (dgDerivedRestriction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a T)ᵒᵖ (finiteOverlapAlgebraVertexToChart R a T).op).map
        (finiteOverlapDerivedRestrictionComparison R a h X) =
      (diagramAlgebraDerivedRestrictionNatTrans (finiteOverlapDGAlgebraDiagram R a) h).app X := by
  exact finiteOverlapAlgebraDerivedRestrictionComparison_Q R a h X.as.obj

end SerrePositivity.KST.DerivedBlowup
