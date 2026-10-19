module

public import
  SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraTransitionComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalComparisonComponents
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparisonComponents

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の 例外因子 Koszul 模型と正規表示の指定加群比較の一致。
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
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：canonical な局所比較の表示不変性。 -/
theorem finiteOverlapExceptionalAlgebraModuleComparison (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (moduleRestriction R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
        (finiteOverlapExceptionalAlgebraVertexToChart R a T).op.op).map
        (finiteOverlapExceptionalModuleComparison R a h M) =
      diagramAlgebraModuleComparison (finiteOverlapExceptionalDGAlgebraDiagram R a) h M := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [moduleRestriction_map_eval]
  change (moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ (op .point)).map
      (finiteOverlapExceptionalModuleComparison R a h M) =
    (moduleEvaluation R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ (op .point)).map
      (diagramAlgebraModuleComparison (finiteOverlapExceptionalDGAlgebraDiagram R a) h M)
  rw [finiteOverlapExceptionalModuleComparison_eval, diagramAlgebraModuleComparison_eval]

end SerrePositivity.KST.DerivedBlowup
