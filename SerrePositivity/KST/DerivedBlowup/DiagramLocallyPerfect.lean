module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleEvaluation
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleProjectiveEnhancement
public import SerrePositivity.DifferentialGraded.Perfect.Basic

/-!
概要：KST §3.1 の全 diagram-module の局所 perfect 条件。
方針：各有限重なりへの実際の導来評価で既存 modulePerfect を要求する。
規約：cartesian 条件はまだ課さず、導来 blowup の最終 Perf と同一視しない。
使われ方：canonical な cartesian 比較を加えて導来 blowup の Perf を定める準備。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：各有限重なりで perfect となる導来図式加群の性質。
方針：実際の導来評価と既存の有限 cell の retract による perfect 条件を使う。
規約：KST §3.1、cartesian 条件と独立の局所条件。
使われ方：導来 blowup の Perf 模型の局所 perfect 部分。 -/
def diagramLocallyPerfect (a : I → R) :
    ObjectProperty (DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :=
  fun M => ∀ T : FiniteOverlapIndex I,
    modulePerfect R (FiniteOverlapVertexObject R a T)ᵒᵖ
      ((finiteOverlapDerivedModuleEvaluation R a T).obj M)

/-- 概要：図式加群の局所 perfect 性は導来同型で不変。
方針：各導来評価で同型を送り、既存 perfect 性の同型不変性を使う。
規約：KST §3.1。使われ方：標準半自由分解による代表の変更。 -/
instance diagramLocallyPerfectClosedUnderIso (a : I → R) :
    (diagramLocallyPerfect R a).IsClosedUnderIsomorphisms where
  of_iso e hM T := (modulePerfect R (FiniteOverlapVertexObject R a T)ᵒᵖ).prop_of_iso
    ((finiteOverlapDerivedModuleEvaluation R a T).mapIso e) (hM T)

/-- 概要：局所 perfect な導来図式加群の充満部分圏。
方針：導来圏内の性質で対象だけを制限する。
規約：KST §3.1、cartesian 条件はまだ加えない。
使われ方：導来 blowup の最終的な局所 perfect な cartesian 部分圏の準備。 -/
abbrev LocallyPerfectDerivedDiagramModules (a : I → R) :=
  (diagramLocallyPerfect R a).FullSubcategory

/-- 概要：射影的な実際の図式加群に対する局所 perfect 条件。
方針：全図式の主導来像に定義済みの局所条件を課す。
規約：KST §3.1。使われ方：導来 mapping 複体を持つ局所 perfect 模型。 -/
def projectiveDiagramLocallyPerfect (a : I → R)
    (M : ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a)) : Prop :=
  diagramLocallyPerfect R a ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj
    (ForgetEnrichment.of (Complex R) M.val))

/-- 概要：局所 perfect な射影的図式加群の充満 dg 部分圏。
方針：全次数 Hom をそのまま保ち、主導来像が局所 perfect な対象に制限する。
規約：KST §3.1、最終的な Perf とするには cartesian 条件がさらに必要。
使われ方：局所 perfect な coherent 図式模型の mapping 複体。 -/
abbrev LocallyPerfectProjectiveDiagramModules (a : I → R) :=
  DGFullSubcategory (ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (projectiveDiagramLocallyPerfect R a)

end SerrePositivity.KST.DerivedBlowup
