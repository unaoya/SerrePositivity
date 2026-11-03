module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraVertexComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraLocallyPerfect
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Functor.Closed

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の一対象正規表示と既存 Koszul 局所模型の perfect 条件の一致。
方針：指定 dg 準同値に沿う導来制限で二つの評価を比較し、既存の perfect 不変性を使う。
規約：全 diagram-module と元の局所 perfect 条件は保持する。
使われ方：正規表示で検証した局所比較を既存の Perf 候補へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：例外因子の元の Koszul 頂点への指定導来評価。
方針：実際の局所埋め込みに沿う導来制限を使う。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：元の局所模型で perfect 性を判定する。 -/
abbrev finiteOverlapExceptionalDerivedModuleEvaluation (a : I → R) (T : FiniteOverlapIndex I) :=
  dgDerivedRestriction R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
    (DiagramModuleCoefficientObject (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ
    (finiteOverlapExceptionalVertexDGFunctor R a T).op

set_option maxHeartbeats 2000000 in
-- 局所 Koszul 模型、正規表示、大域係数圏の三つの導来制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数から基底環へ制限した dg 構造を照合するために必要。
/-- 概要：元の局所評価を正規表示へ制限すると正規表示での評価になる。
方針：二つの大域埋め込みの整合性に標準導来制限合成同型を適用する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：二つの局所 perfect 条件の比較同型。 -/
def finiteOverlapExceptionalAlgebraDerivedEvaluationComparison (a : I → R)
    (T : FiniteOverlapIndex I) :
    finiteOverlapExceptionalDerivedModuleEvaluation R a T ⋙
        dgDerivedRestriction R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
          (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
          (finiteOverlapExceptionalAlgebraVertexToChart R a T).op ≅
      diagramAlgebraDerivedEvaluation (finiteOverlapExceptionalDGAlgebraDiagram R a) T :=
  transitionDerivedRestrictionCompIso (finiteOverlapExceptionalAlgebraVertexToChart R a T)
    (finiteOverlapExceptionalVertexDGFunctor R a T)
    (diagramAlgebraVertexEmbedding (finiteOverlapExceptionalDGAlgebraDiagram R a) T)
    (finiteOverlapExceptionalAlgebraVertexToChart_embedding R a T)

set_option maxHeartbeats 2000000 in
-- 指定 dg 準同値と opposite 後の二つの perfect 条件を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化 dg 模型と正規表示の導来加群圏の構造を照合するために必要。
/-- 概要：正規表示での局所 perfect 性は元の Koszul 模型での局所 perfect 性と一致する。
方針：評価比較同型と指定 dg 準同値に沿う perfect 性の不変性を合成する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：既存の局所 perfect 条件を正規表示でも使える保証。 -/
theorem finiteOverlapExceptionalAlgebraPerfect_iff (a : I → R) (T : FiniteOverlapIndex I)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    modulePerfect R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
        ((diagramAlgebraDerivedEvaluation (finiteOverlapExceptionalDGAlgebraDiagram R a) T).obj X) ↔
      modulePerfect R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
        ((finiteOverlapExceptionalDerivedModuleEvaluation R a T).obj X) := by
  have hΓ := quasiEquivalence_op (finiteOverlapExceptionalAlgebraVertexToChart R a T)
    (finiteOverlapExceptionalAlgebraVertexToChart_quasiEquivalence R a T)
  exact ((modulePerfect R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ).prop_iff_of_iso
    ((finiteOverlapExceptionalAlgebraDerivedEvaluationComparison R a T).app X)).symm.trans
      (quasiEquivalenceRestriction_perfect_iff R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
        (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
        (finiteOverlapExceptionalAlgebraVertexToChart R a T).op hΓ
        ((finiteOverlapExceptionalDerivedModuleEvaluation R a T).obj X))

end SerrePositivity.KST.DerivedBlowup
