module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnderlyingDiagram

/-!
概要：KST §3.1 の正規表示に沿う指定局所加群比較の成分計算。
方針：制限合成同型の恒等成分と指定単位矢の加群作用を評価する。
規約：基底環上の underlying 図式と係数拡大の cartesian 比較は区別する。
使われ方：単位・三重整合性を複体図式の関手性へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示の一段・二段の制限合成比較の評価は恒等。
方針：既存の加群制限合成同型の逆の恒等成分を使う。
規約：KST §3.1。使われ方：指定加群比較を評価する際の標準同型の消去。 -/
theorem diagramAlgebraCompositeEvaluationIso_hom_eval {i j : J} (h : i ≤ j)
    (M : AllDiagramModules F) (x : (AlgebraVertex (F.obj i))ᵒᵖ) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ x).map
      ((diagramAlgebraCompositeEvaluationIso F h).hom.app M) = 𝟙 _ := by
  change (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ x).map
    (moduleRestrictionCompObjIso R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
      (DiagramModuleCoefficientObject F)ᵒᵖ (diagramAlgebraVertexTransition F h).op.op
      (diagramAlgebraVertexEmbedding F j).op.op M).inv = 𝟙 _
  exact moduleIsoMk_inv_eval R _ _ _ x

/-- 概要：正規表示の指定局所加群比較の標準点での評価。
方針：全次数自然変換の加群作用と制限合成同型の成分を計算する。
規約：KST §3.1。使われ方：underlying 図式の指定包含写像との同定。 -/
theorem diagramAlgebraModuleComparison_eval {i j : J} (h : i ≤ j) (M : AllDiagramModules F) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramAlgebraModuleComparison F h M) =
      (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) := by
  change (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
    (transitionModuleMorphism (diagramAlgebraVertexTransformation F h)
      (ForgetEnrichment.to (Complex R) M) ≫
      (diagramAlgebraCompositeEvaluationIso F h).hom.app M) = _
  rw [Functor.map_comp, diagramAlgebraCompositeEvaluationIso_hom_eval,
    transitionModuleMorphism_eval, diagramModuleUnderlyingDiagram_map]
  change mapFromUnit R _ _ (diagramModuleTransitionUnit F h ≫
      (ForgetEnrichment.to (Complex R) M).map (op (op ⟨i⟩)) (op (op ⟨j⟩))) ≫
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨j⟩))) = _
  exact Category.comp_id _

/-- 概要：任意の局所対象での指定加群比較の評価。
方針：正規表示の一対象性によって標準点へ帰着する。
規約：KST §3.1。使われ方：局所遷移で制限した比較を評価する。 -/
theorem diagramAlgebraModuleComparison_eval_any {i j : J} (h : i ≤ j)
    (M : AllDiagramModules F) (x : (AlgebraVertex (F.obj i))ᵒᵖ) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ x).map
      (diagramAlgebraModuleComparison F h M) =
      (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) := by
  have hx : x = op .point := by
    apply Opposite.unop_injective
    cases x.unop
    rfl
  subst x
  exact diagramAlgebraModuleComparison_eval F h M

end SerrePositivity.KST.DerivedBlowup
