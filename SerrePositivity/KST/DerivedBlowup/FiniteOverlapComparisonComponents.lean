module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnderlyingDiagram

/-!
概要：KST §3.1 の指定局所加群比較の underlying 成分。
方針：全次数 Hom の評価公式と制限合成同型の恒等成分を使う。
規約：導来係数拡大の比較射と underlying の単位矢作用を区別する。
使われ方：指定比較の恒等・三重整合性を証明するための成分計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：一段・二段の制限比較の underlying 成分は恒等。
方針：既存の加群制限の合成比較の逆射を評価する。
規約：KST §3.1。使われ方：canonical な局所加群比較の成分計算。 -/
theorem finiteOverlapCompositeEvaluationIso_hom_eval (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (x : (FiniteOverlapVertexObject R a T)ᵒᵖ) :
    (moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ x).map
      ((finiteOverlapCompositeEvaluationIso R a h).hom.app M) = 𝟙 _ := by
  change (moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ x).map
    (moduleRestrictionCompObjIso R (FiniteOverlapVertexObject R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ (BlowupDiagramCoefficientObject R a)ᵒᵖ
      (finiteOverlapLocalDGTransition R a h).op.op
      (finiteOverlapVertexDGFunctor R a U).op.op M).inv = 𝟙 _
  exact moduleIsoMk_inv_eval R _ _ _ x

/-- 概要：指定局所加群比較の成分は underlying 図式の指定包含写像。
方針：全次数 Hom の評価公式と標準合成比較の恒等成分を使う。
規約：KST §3.1。使われ方：図式全体の恒等・三重整合性との接続。 -/
theorem finiteOverlapModuleComparison_eval (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ (op .point)).map
      (finiteOverlapModuleComparison R a h M) =
      (diagramModuleUnderlyingDiagram (finiteOverlapDGAlgebraDiagram R a)
        (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) := by
  rw [finiteOverlapModuleComparison, Functor.map_comp,
    finiteOverlapCompositeEvaluationIso_hom_eval, Category.comp_id]
  change (moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ (op .point)).map
    (transitionModuleMorphism (finiteOverlapTransitionGradedNatTrans R a h)
      (ForgetEnrichment.to (Complex R) M)) = _
  rw [transitionModuleMorphism_eval, diagramModuleUnderlyingDiagram_map]
  rfl

end SerrePositivity.KST.DerivedBlowup
