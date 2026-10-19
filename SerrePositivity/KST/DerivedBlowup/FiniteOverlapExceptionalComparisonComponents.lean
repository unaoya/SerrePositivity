module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalModuleComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnderlyingDiagram

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の指定局所加群比較の underlying 成分。
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
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：canonical な局所加群比較の成分計算。 -/
theorem finiteOverlapExceptionalCompositeEvaluationIso_hom_eval (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a))
    (x : (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ) :
    (moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ x).map
      ((finiteOverlapExceptionalCompositeEvaluationIso R a h).hom.app M) = 𝟙 _ := by
  change (moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ x).map
    (moduleRestrictionCompObjIso R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ (DiagramModuleCoefficientObject
        (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ
      (finiteOverlapExceptionalLocalDGTransition R a h).op.op
      (finiteOverlapExceptionalVertexDGFunctor R a U).op.op M).inv = 𝟙 _
  exact moduleIsoMk_inv_eval R _ _ _ x

/-- 概要：指定局所加群比較の成分は underlying 図式の指定包含写像。
方針：全次数 Hom の評価公式と標準合成比較の恒等成分を使う。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：図式全体の恒等・三重整合性との接続。 -/
theorem finiteOverlapExceptionalModuleComparison_eval (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ (op .point)).map
      (finiteOverlapExceptionalModuleComparison R a h M) =
      (diagramModuleUnderlyingDiagram (finiteOverlapExceptionalDGAlgebraDiagram R a)
        (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) := by
  rw [finiteOverlapExceptionalModuleComparison, Functor.map_comp,
    finiteOverlapExceptionalCompositeEvaluationIso_hom_eval, Category.comp_id]
  change (moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ (op .point)).map
    (transitionModuleMorphism (finiteOverlapExceptionalTransitionGradedNatTrans R a h)
      (ForgetEnrichment.to (Complex R) M)) = _
  rw [transitionModuleMorphism_eval, diagramModuleUnderlyingDiagram_map]
  rfl

/-- 概要：任意の局所対象での指定加群比較の評価は指定包含写像。
方針：局所 dg 模型の一対象性で標準点での評価公式へ戻す。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：遷移後の対象を正規化せず三重比較を計算する。 -/
theorem finiteOverlapExceptionalModuleComparison_eval_any (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a))
    (x : (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ) :
    (moduleEvaluation R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ x).map
      (finiteOverlapExceptionalModuleComparison R a h M) =
      (diagramModuleUnderlyingDiagram (finiteOverlapExceptionalDGAlgebraDiagram R a)
        (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) := by
  have hx : x = op .point := by
    apply Opposite.unop_injective
    cases x.unop
    rfl
  subst x
  exact finiteOverlapExceptionalModuleComparison_eval R a h M

end SerrePositivity.KST.DerivedBlowup
