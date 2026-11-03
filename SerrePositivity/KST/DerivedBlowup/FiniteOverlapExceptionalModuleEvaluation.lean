module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalVertex
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の各非空有限重なりへの全 diagram-module の導来評価。
方針：局所 dg 模型の埋め込みの opposite に沿って既存の加群制限を適用する。
規約：擬同型を保つため評価自体は置換を要さず、全図式の導来局所化へ降りる。
使われ方：局所 perfect 条件と canonical な cartesian 比較の局所評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：全 diagram-module の一つの有限重なりへの加群評価。
方針：局所埋め込みの opposite に沿って右 dg 加群を制限する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：局所模型への実際の加群評価関手。 -/
def finiteOverlapExceptionalModuleEvaluation (a : I → R) (T : FiniteOverlapIndex I) :
    AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a) ⥤
      ModuleCategory R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ :=
  moduleRestriction R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
    (DiagramModuleCoefficientObject (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ
      (finiteOverlapExceptionalVertexDGFunctor R a T).op.op

/-- 概要：有限重なりへの加群評価は objectwise 擬同型を保つ。
方針：dg 加群制限の一般の擬同型保存を適用する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：評価を主導来局所化へ降ろす。 -/
theorem finiteOverlapExceptionalModuleEvaluation_quasiIso (a : I → R) (T : FiniteOverlapIndex I)
    {M N : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)} (f : M ⟶ N)
    (hf : moduleQuasiIso R (DiagramModuleCoefficientObject
      (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ f) :
    moduleQuasiIso R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
      ((finiteOverlapExceptionalModuleEvaluation R a T).map f) :=
  moduleRestriction_quasiIso R _ _ _ f hf

/-- 概要：局所評価の underlying 複体は元の図式加群の当該添字での値。
方針：dg 加群制限と評価の合成の一般公式を適用する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：局所評価が実際の切断値であることの確認。 -/
theorem finiteOverlapExceptionalModuleEvaluation_comp_value (a : I → R)
    (T : FiniteOverlapIndex I) :
    finiteOverlapExceptionalModuleEvaluation R a T ⋙
      moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ (op .point) =
    moduleEvaluation R (DiagramModuleCoefficientObject
      (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ (op ⟨T⟩) :=
  moduleRestriction_comp_evaluation R _ _ _ _

end SerrePositivity.KST.DerivedBlowup
