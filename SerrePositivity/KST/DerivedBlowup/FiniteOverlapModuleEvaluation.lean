module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapVertex
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits

/-!
概要：KST §3.1 の各非空有限重なりへの全 diagram-module の導来評価。
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
規約：KST §3.1。使われ方：局所模型への実際の加群評価関手。 -/
def finiteOverlapModuleEvaluation (a : I → R) (T : FiniteOverlapIndex I) :
    AllDiagramModules (finiteOverlapDGAlgebraDiagram R a) ⥤
      ModuleCategory R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  moduleRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (BlowupDiagramCoefficientObject R a)ᵒᵖ (finiteOverlapVertexDGFunctor R a T).op.op

/-- 概要：有限重なりへの加群評価は objectwise 擬同型を保つ。
方針：dg 加群制限の一般の擬同型保存を適用する。
規約：KST §3.1。使われ方：評価を主導来局所化へ降ろす。 -/
theorem finiteOverlapModuleEvaluation_quasiIso (a : I → R) (T : FiniteOverlapIndex I)
    {M N : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)} (f : M ⟶ N)
    (hf : moduleQuasiIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ f) :
    moduleQuasiIso R (FiniteOverlapVertexObject R a T)ᵒᵖ
      ((finiteOverlapModuleEvaluation R a T).map f) :=
  moduleRestriction_quasiIso R _ _ _ f hf

/-- 概要：全 diagram-module の主導来圏から各有限重なりの導来加群圏への評価。
方針：構成済みの dg 関手に沿う導来制限を適用する。
規約：KST §3.1。使われ方：局所 perfect 条件の実際の評価関手。 -/
def finiteOverlapDerivedModuleEvaluation (a : I → R) (T : FiniteOverlapIndex I) :
    DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a) ⥤
      DerivedModuleCategory R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  dgDerivedRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (BlowupDiagramCoefficientObject R a)ᵒᵖ (finiteOverlapVertexDGFunctor R a T).op

/-- 概要：有限重なりの導来評価は実際の加群評価と主局所化の比較を満たす。
方針：導来制限の構成された因子分解等式を使う。
規約：KST §3.1。使われ方：置換した図式加群の局所評価の計算。 -/
theorem finiteOverlapDerivedModuleEvaluation_fac (a : I → R) (T : FiniteOverlapIndex I) :
    moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ ⋙
      finiteOverlapDerivedModuleEvaluation R a T =
    finiteOverlapModuleEvaluation R a T ⋙
      moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  dgDerivedRestriction_fac R _ _ _

/-- 概要：局所評価の underlying 複体は元の図式加群の当該添字での値。
方針：dg 加群制限と評価の合成の一般公式を適用する。
規約：KST §3.1。使われ方：局所評価が実際の切断値であることの確認。 -/
theorem finiteOverlapModuleEvaluation_comp_value (a : I → R) (T : FiniteOverlapIndex I) :
    finiteOverlapModuleEvaluation R a T ⋙
      moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ (op .point) =
    moduleEvaluation R (BlowupDiagramCoefficientObject R a)ᵒᵖ (op ⟨T⟩) :=
  moduleRestriction_comp_evaluation R _ _ _ _

end SerrePositivity.KST.DerivedBlowup
