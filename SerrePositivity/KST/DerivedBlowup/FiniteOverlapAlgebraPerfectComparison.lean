module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraVertexComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraLocallyPerfect
public import SerrePositivity.KST.DerivedBlowup.DiagramLocallyPerfect
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalence
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalenceOpposite

/-!
概要：KST §3.1 の一対象正規表示と既存 Koszul 局所模型の perfect 条件の一致。
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

set_option maxHeartbeats 2000000 in
-- 局所 Koszul 模型、正規表示、大域係数圏の三つの導来制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数から基底環へ制限した dg 構造を照合するために必要。
/-- 概要：元の局所評価を正規表示へ制限すると正規表示での評価になる。
方針：二つの大域埋め込みの整合性に標準導来制限合成同型を適用する。
規約：KST §3.1。使われ方：二つの局所 perfect 条件の比較同型。 -/
def finiteOverlapAlgebraDerivedEvaluationComparison (a : I → R) (T : FiniteOverlapIndex I) :
    finiteOverlapDerivedModuleEvaluation R a T ⋙
        dgDerivedRestriction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
          (FiniteOverlapVertexObject R a T)ᵒᵖ (finiteOverlapAlgebraVertexToChart R a T).op ≅
      diagramAlgebraDerivedEvaluation (finiteOverlapDGAlgebraDiagram R a) T :=
  transitionDerivedRestrictionCompIso (finiteOverlapAlgebraVertexToChart R a T)
    (finiteOverlapVertexDGFunctor R a T)
    (diagramAlgebraVertexEmbedding (finiteOverlapDGAlgebraDiagram R a) T)
    (finiteOverlapAlgebraVertexToChart_embedding R a T)

set_option maxHeartbeats 2000000 in
-- 指定 dg 準同値と opposite 後の二つの perfect 条件を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化 dg 模型と正規表示の導来加群圏の構造を照合するために必要。
/-- 概要：正規表示での局所 perfect 性は元の Koszul 模型での局所 perfect 性と一致する。
方針：評価比較同型と指定 dg 準同値に沿う perfect 性の不変性を合成する。
規約：KST §3.1。使われ方：既存の局所 perfect 条件を正規表示でも使える保証。 -/
theorem finiteOverlapAlgebraPerfect_iff (a : I → R) (T : FiniteOverlapIndex I)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    modulePerfect R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
        ((diagramAlgebraDerivedEvaluation (finiteOverlapDGAlgebraDiagram R a) T).obj X) ↔
      modulePerfect R (FiniteOverlapVertexObject R a T)ᵒᵖ
        ((finiteOverlapDerivedModuleEvaluation R a T).obj X) := by
  have hΓ := quasiEquivalence_op (finiteOverlapAlgebraVertexToChart R a T)
    (finiteOverlapAlgebraVertexToChart_quasiEquivalence R a T)
  exact ((modulePerfect R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ).prop_iff_of_iso
    ((finiteOverlapAlgebraDerivedEvaluationComparison R a T).app X)).symm.trans
      (quasiEquivalenceRestriction_perfect_iff R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
        (FiniteOverlapVertexObject R a T)ᵒᵖ (finiteOverlapAlgebraVertexToChart R a T).op hΓ
        ((finiteOverlapDerivedModuleEvaluation R a T).obj X))

/-- 概要：全有限重なりでの正規表示の局所 perfect 条件は既存条件に一致する。
方針：各頂点での構成済み iff を全称化する。
規約：KST §3.1。使われ方：同じ大域 Perf 候補での局所表示の変更。 -/
theorem finiteOverlapAlgebraLocallyPerfect_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramAlgebraLocallyPerfect (finiteOverlapDGAlgebraDiagram R a) X ↔
      diagramLocallyPerfect R a X :=
  forall_congr' (fun T => finiteOverlapAlgebraPerfect_iff R a T X)

end SerrePositivity.KST.DerivedBlowup
