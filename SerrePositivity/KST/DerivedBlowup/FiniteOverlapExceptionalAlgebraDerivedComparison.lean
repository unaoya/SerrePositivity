module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraModuleComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の指定導来制限比較の正規表示との一致。
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
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：canonical な導来比較の表示比較。 -/
theorem finiteOverlapExceptionalAlgebraDerivedRestrictionComparison_Q (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (dgDerivedRestriction R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
        (finiteOverlapExceptionalAlgebraVertexToChart R a T).op).map
        ((finiteOverlapExceptionalDerivedRestrictionNatTrans R a h).app
          ((moduleToDerived R (DiagramModuleCoefficientObject
            (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).obj M)) =
      (diagramAlgebraDerivedRestrictionNatTrans (finiteOverlapExceptionalDGAlgebraDiagram R a)
        h).app
        ((moduleToDerived R (DiagramModuleCoefficientObject
          (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).obj M) := by
  rw [finiteOverlapExceptionalDerivedRestrictionNatTrans_app_Q_map,
    diagramAlgebraDerivedRestrictionNatTrans_app_Q_map,
    transitionDerivedRestriction_map_Q, finiteOverlapExceptionalAlgebraModuleComparison]

set_option maxHeartbeats 2000000 in
-- 正規表示と元の局所導来制限の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の dg 加群圏を照合するために必要。
/-- 概要：全導来対象で指定導来制限比較は正規表示への制限と整合する。
方針：主局所化の対象が保持する実加群に計算公式を適用する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：二つの表示の随伴比較の同定。 -/
theorem finiteOverlapExceptionalAlgebraDerivedRestrictionComparison (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (dgDerivedRestriction R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
        (finiteOverlapExceptionalAlgebraVertexToChart R a T).op).map
        (finiteOverlapExceptionalDerivedRestrictionComparison R a h X) =
      (diagramAlgebraDerivedRestrictionNatTrans (finiteOverlapExceptionalDGAlgebraDiagram R a)
        h).app X := by
  exact finiteOverlapExceptionalAlgebraDerivedRestrictionComparison_Q R a h X.as.obj

end SerrePositivity.KST.DerivedBlowup
