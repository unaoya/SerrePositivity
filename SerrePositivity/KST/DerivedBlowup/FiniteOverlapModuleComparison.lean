module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTransitionTransformation
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleEvaluation
public import SerrePositivity.KST.DerivedBlowup.TransitionModuleAction
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence

/-!
概要：KST §3.1 の図式加群の canonical な局所制限比較射。
方針：指定の単位矢の全次数自然変換を加群へ作用させ、制限の合成比較を接続する。
規約：存在を仮定せず、指定の包含射から実際の dg 加群射を構成する。
使われ方：導来係数拡大–制限随伴で cartesian 比較射を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：選択 pivot の局所模型間の共通基底環上の dg 遷移。
方針：既存の有限重なり遷移を非空有限集合の選択表示に適用する。
規約：KST §3.1。使われ方：局所加群比較の係数 dg 関手。 -/
abbrev finiteOverlapLocalDGTransition (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :=
  finiteOverlapBaseDGTransition R a (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
    h (finiteOverlapIndexPivot_mem T)

/-- 概要：遷移後の埋め込みに沿って一度で制限した図式加群。
方針：局所遷移と目標の埋め込みの合成に沿って制限する。
規約：KST §3.1。使われ方：指定自然変換を直接作用させた比較の行先。 -/
def finiteOverlapCompositeModuleEvaluation (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    AllDiagramModules (finiteOverlapDGAlgebraDiagram R a) ⥤
      ModuleCategory R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  moduleRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (BlowupDiagramCoefficientObject R a)ᵒᵖ
    ((finiteOverlapLocalDGTransition R a h).comp (finiteOverlapVertexDGFunctor R a U)).op.op

/-- 概要：目標で評価してから局所遷移に沿って制限した図式加群。
方針：目標の評価と局所制限を順に適用する。
規約：KST §3.1。使われ方：導来係数拡大–制限随伴の右辺。 -/
def finiteOverlapIteratedModuleEvaluation (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    AllDiagramModules (finiteOverlapDGAlgebraDiagram R a) ⥤
      ModuleCategory R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  finiteOverlapModuleEvaluation R a U ⋙ moduleRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op.op

/-- 概要：一段と二段の局所加群制限の標準自然同型。
方針：既存の dg 制限合成比較を二重 opposite の合成に適用する。
規約：KST §3.1。使われ方：指定比較射を反復制限の行先へ送る。 -/
def finiteOverlapCompositeEvaluationIso (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapCompositeModuleEvaluation R a h ≅ finiteOverlapIteratedModuleEvaluation R a h := by
  unfold finiteOverlapCompositeModuleEvaluation finiteOverlapIteratedModuleEvaluation
  simp only [DGFunctor.op_comp]
  exact (moduleRestrictionCompIso R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ (BlowupDiagramCoefficientObject R a)ᵒᵖ
    (finiteOverlapLocalDGTransition R a h).op.op (finiteOverlapVertexDGFunctor R a U).op.op).symm

set_option maxHeartbeats 4000000 in
-- 局所化環の全次数自然変換と実際の加群評価の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の dg 模型と共通基底環上の係数圏を照合するために必要。
/-- 概要：指定単位矢から合成埋め込みへの実際の局所加群比較射。
方針：指定 GradedNatTrans の加群への作用を適用する。
規約：KST §3.1。使われ方：canonical な局所加群の比較射の前半。 -/
def finiteOverlapModuleComparisonToComposite (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapModuleEvaluation R a T).obj M ⟶
      (finiteOverlapCompositeModuleEvaluation R a h).obj M :=
  transitionModuleMorphism (finiteOverlapTransitionGradedNatTrans R a h)
    (ForgetEnrichment.to (Complex R) M)

/-- 概要：図式加群の元の局所評価から遷移で制限した目標評価への canonical な比較射。
方針：指定単位矢の作用に一段・二段の制限合成比較を続ける。
規約：KST §3.1、置換や任意同型の選択を含まない指定射。
使われ方：導来係数拡大の canonical な cartesian 比較の入力。 -/
def finiteOverlapModuleComparison (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapModuleEvaluation R a T).obj M ⟶
      (finiteOverlapIteratedModuleEvaluation R a h).obj M :=
  finiteOverlapModuleComparisonToComposite R a h M ≫
    (finiteOverlapCompositeEvaluationIso R a h).hom.app M

end SerrePositivity.KST.DerivedBlowup
