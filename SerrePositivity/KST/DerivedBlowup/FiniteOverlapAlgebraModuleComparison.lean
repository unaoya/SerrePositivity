module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraTransitionComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapComparisonComponents
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparisonComponents

/-!
概要：KST §3.1 の Koszul チャートと正規表示の指定加群比較の一致。
方針：Hom 恒等の表示比較に沿って制限し、指定包含射の作用を評価する。
規約：比較する射は両表示で構成した canonical な加群射。
使われ方：二つの cartesian 条件を導来局所化上で比較する入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 二つの局所化環から制限された加群構造を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の dg 加群の構造を照合するために必要。
/-- 概要：元の指定加群比較を正規表示へ制限すると正規表示の指定比較になる。
方針：一対象正規表示で加群射を評価し、共通の underlying 包含写像へ帰着する。
規約：KST §3.1。使われ方：canonical な局所比較の表示不変性。 -/
theorem finiteOverlapAlgebraModuleComparison (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (moduleRestriction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a T)ᵒᵖ (finiteOverlapAlgebraVertexToChart R a T).op.op).map
        (finiteOverlapModuleComparison R a h M) =
      diagramAlgebraModuleComparison (finiteOverlapDGAlgebraDiagram R a) h M := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [moduleRestriction_map_eval]
  change (moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ (op .point)).map
      (finiteOverlapModuleComparison R a h M) =
    (moduleEvaluation R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ (op .point)).map
      (diagramAlgebraModuleComparison (finiteOverlapDGAlgebraDiagram R a) h M)
  rw [finiteOverlapModuleComparison_eval, diagramAlgebraModuleComparison_eval]

end SerrePositivity.KST.DerivedBlowup
