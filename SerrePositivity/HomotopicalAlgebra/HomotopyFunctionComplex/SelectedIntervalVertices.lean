module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints

/-! # The entire vertex cylinder remains fixed in the same selected interval system -/

@[expose] public section
universe v u uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev vertices := NerveCylinderBoundary.product
  (ResolutionArrowComparisonEndpoints.vertexParameter C)
  ResolutionArrowCylinderBoundary.interval.{max u v}
abbrev horizontal : vertices C ⟶ ResolutionArrowCylinderBoundary.fullParameter C :=
  NerveCylinderBoundary.horizontal (ResolutionArrowComparisonEndpoints.vertexParameter C)
    (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.vertexInclusion C)
    ResolutionArrowCylinderBoundary.interval.{max u v}

lemma coherent_vertices : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
    (SelectedIntervalDiagram.forget C ⋙ vertices C) (SelectedIntervalDiagram.parameters C)
    (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C) (horizontal C)) =
    reindex (vertices C)
      (NerveMovingParameter.lifted (ResolutionArrowComparisonEndpoints.values C))
      (SelectedIntervalDiagram.forget C) (ResolutionArrowCylinderBoundary.vertices C) := by
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (NerveCylinderBoundary.horizontal _ _ _ _)) = _
  rw [← NerveCylinderBoundary.vertexInclusion_inclusion
    (ResolutionArrowComparisonEndpoints.vertexParameter C)
    (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.vertexInclusion C)
    ResolutionArrowCylinderBoundary.boundaryMap.{max u v}]
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (NerveCylinderBoundary.vertexInclusion _ _ _ _) ≫
        SelectedIntervalDiagram.boundaryInclusion C) = _
  have hb : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
      (SelectedIntervalDiagram.boundaries C) (SelectedIntervalDiagram.parameters C)
      (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
      (SelectedIntervalDiagram.boundaryInclusion C) =
      SelectedIntervalDiagram.fixedBoundary C hcof :=
    SelectedIntervalDiagram.coherent_boundary C hcof hfib
  rw [← restriction_comp, ← Category.assoc, hb]
  change reindex _ _ (SelectedIntervalDiagram.forget C)
    (ResolutionArrowCylinderBoundary.system C hcof) ≫ restriction _ _ _
      (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
        (NerveCylinderBoundary.vertexInclusion _ _ _ _)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_vertices]

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ SelectedIntervalDiagram.Index C)

lemma reindexed_vertices : reindex (SelectedIntervalDiagram.parameters C)
    (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) H
      (SelectedIntervalDiagram.coherent C hcof hfib) ≫ restriction _ _ _
        (Functor.whiskerLeft H
          (Functor.whiskerLeft (SelectedIntervalDiagram.forget C) (horizontal C))) =
    NerveNaturalBoundary.ofNatTrans _ _ (Functor.whiskerLeft
      (H ⋙ SelectedIntervalDiagram.forget C)
      (NerveProductParameter.projection (ResolutionArrowComparisonEndpoints.vertexParameter C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
          ResolutionArrowComparisonEndpoints.vertexBoundary C)) := by
  rw [← reindex_restriction, coherent_vertices]
  apply (reindex_reindex (vertices C)
    (NerveMovingParameter.lifted (ResolutionArrowComparisonEndpoints.values C))
    (SelectedIntervalDiagram.forget C) H (ResolutionArrowCylinderBoundary.vertices C)).trans
  exact reindex_natural _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices
