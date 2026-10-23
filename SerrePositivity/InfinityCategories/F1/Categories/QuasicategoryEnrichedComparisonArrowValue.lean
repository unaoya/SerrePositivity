module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramArrow
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramDiagonalArrow
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramRealizationVertices

/-!
概要：全局所 Hom に自然な比較の arrow 図式を、同じ通常の自然変換と同定する。
方針：区間の両端と全射を照合し、既存の頂点実現へ渡す。
規約：底全体の図式と元の比較成分を保持する。
使われ方：結合比較の全局所族と既存の区間族の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance quasicategoryComparisonArrowValue_sourceCore_simplicialCategory
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E : QuasicategoryEnrichedDiagram C J}
  (η : QuasicategoryEnrichedDiagramComparison D E)
  (X : TransportEnrichment quasicategoryCoreFunctor.{u} C)

/-- 元の比較を固定した arrow 図式は、同じ通常の自然変換の積上の図式。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrow_value :
    quasicategoryDiagramValueFunctor (η.arrowDiagram.toCoreEnrichedFunctor.obj X) =
      qCatDiagramArrow (quasicategoryDiagramQCatTransformation
        (F := D.toCoreEnrichedFunctor.obj X) (G := E.toCoreEnrichedFunctor.obj X)
        (Functor.whiskerRight (η.evaluate X) quasicategoryObjectForget)) := by
  refine CategoryTheory.Functor.ext (fun ⟨i, a⟩ ↦ by fin_cases i <;> rfl) ?_
  rintro ⟨i, a⟩ ⟨j, b⟩ f
  fin_cases i <;> fin_cases j
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals rfl

/-- 同じ全局所比較の実現を一対象に固定すると、元の積上の図式全体となる。 -/
lemma QuasicategoryEnrichedDiagramComparison.realization_vertex :
    η.arrowDiagram.realization.app (Opposite.op ⦋0⦌) (coherentNerveVertex X) =
      functorVertex (qCatDiagramCoherentNerve
        (qCatDiagramArrow (quasicategoryDiagramQCatTransformation
          (F := D.toCoreEnrichedFunctor.obj X) (G := E.toCoreEnrichedFunctor.obj X)
          (Functor.whiskerRight (η.evaluate X) quasicategoryObjectForget)))) := by
  exact (η.arrowDiagram.realization_vertex X).trans
    (congrArg (fun F ↦ functorVertex (qCatDiagramCoherentNerve F)) (η.arrow_value X))

end SerrePositivity.InfinityCategories
