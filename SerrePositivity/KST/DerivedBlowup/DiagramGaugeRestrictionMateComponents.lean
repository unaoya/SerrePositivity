module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeRestrictionMate

/-!
概要：KST §3.1 の graph 重みの制限側 mate を各斉次元で計算する。
方針：単位で tensor に挿入し、graph 因子を重み付けし、余単位で評価する。
規約：重みは次数零であり、余分な Koszul 符号を残さない。
使われ方：捻りの指定図式遷移と制限側 mate の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

set_option maxHeartbeats 2000000 in
-- 指定随伴の成分と graph の tensor の元の型を照合するために必要。
/-- 概要：指定制限側 mate の成分は重み付けされた次数零単位の加群作用。
方針：単位挿入・graph 重み付け・余単位評価の三つを純斉次元で計算する。
規約：KST §3.1。使われ方：任意図式加群の指定捻り遷移の計算。 -/
theorem diagramGaugeModuleRestrictionIso_apply {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (F.obj j))ᵒᵖ) (r : ℤ)
    (m : ((ForgetEnrichment.to (Complex R) M).obj (op (op .point))).X r) :
    (((moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      ((diagramGaugeModuleRestrictionIso F s h).hom.app M)).f r) m =
    moduleAction R (ForgetEnrichment.to (Complex R) M)
      (((s.scale h).hom.f 0)
        (unitElement R (op (.point : AlgebraVertex (F.obj j)))).val) m (add_zero r) := by
  rw [diagramGaugeModuleRestrictionIso_hom_app,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleRestriction_map_eval, moduleRestriction_map_eval]
  dsimp only [dgModuleUnit, dgModuleCounit]
  rw [functorExtensionUnit_eval, functorExtensionCounit_eval]
  change (functorExtensionEvaluationComponent R
      (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
      (diagramAlgebraVertexTransition F h).op (ForgetEnrichment.to (Complex R) M) (op .point)).f r
    ((((moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
      ((diagramGaugeModuleExtensionIso F s h).hom.app
        ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).obj M))).f r)
      ((functorExtensionInsertionComponent R
        (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op
        (restrictModule R _ _ (diagramAlgebraVertexTransition F h).op.op
          (ForgetEnrichment.to (Complex R) M)) (op .point)).f r m)) = _
  rw [functorExtensionInsertion_apply]
  have he := diagramGaugeModuleExtensionIso_element F s h
    ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).obj M)
    (show ((ForgetEnrichment.to (Complex R)
      ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).obj M)).obj
      (op (op .point))).X r from m)
    (unitElement R (op (.point : AlgebraVertex (F.obj j)))).val (add_zero r)
  refine (congrArg (fun z => (functorExtensionEvaluationComponent R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op (ForgetEnrichment.to (Complex R) M)
    (op .point)).f r z) he).trans ?_
  have hc := functorExtensionEvaluation_element R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op (ForgetEnrichment.to (Complex R) M)
    (op .point) (op .point) m
    (((s.scale h).hom.f 0) (unitElement R (op (.point : AlgebraVertex (F.obj j)))).val)
    (add_zero r)
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at hc
  change (functorExtensionEvaluationComponent R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op (ForgetEnrichment.to (Complex R) M) (op .point)).f r
    (BalancedTensor.element R (AlgebraVertex (F.obj i))ᵒᵖ
      (restrictModule R _ _ (diagramAlgebraVertexTransition F h).op.op
        (ForgetEnrichment.to (Complex R) M))
      ((functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).leftAt (op .point)) (op .point) m
      (((s.scale h).hom.f 0)
        (unitElement R (op (.point : AlgebraVertex (F.obj j)))).val) (add_zero r)) = _
  exact hc

end SerrePositivity.KST.DerivedBlowup
