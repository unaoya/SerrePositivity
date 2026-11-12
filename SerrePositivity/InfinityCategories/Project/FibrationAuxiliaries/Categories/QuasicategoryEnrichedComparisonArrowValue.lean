module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramArrow
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramDiagonalArrow
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramRealizationVertices

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
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

local instance quasicategoryComparisonArrowValue_sourceCore_simplicialCategory
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
  (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
  (X : TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C)

/-- 元の比較を固定した arrow 図式は、同じ通常の自然変換の積上の図式。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrow_value :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValueFunctor (η.arrowDiagram.toCoreEnrichedFunctor.obj X) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramQCatTransformation
        (F := D.toCoreEnrichedFunctor.obj X) (G := E.toCoreEnrichedFunctor.obj X)
        (Functor.whiskerRight (η.evaluate X) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)) := by
  refine CategoryTheory.Functor.ext (fun ⟨i, a⟩ ↦ by fin_cases i <;> rfl) ?_
  rintro ⟨i, a⟩ ⟨j, b⟩ f
  fin_cases i <;> fin_cases j
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals rfl

/-- 同じ全局所比較の実現を一対象に固定すると、元の積上の図式全体となる。 -/
lemma QuasicategoryEnrichedDiagramComparison.realization_vertex :
    η.arrowDiagram.realization.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramQCatTransformation
          (F := D.toCoreEnrichedFunctor.obj X) (G := E.toCoreEnrichedFunctor.obj X)
          (Functor.whiskerRight (η.evaluate X) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)))) := by
  exact (η.arrowDiagram.realization_vertex X).trans
    (congrArg (fun F ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F)) (η.arrow_value X))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
