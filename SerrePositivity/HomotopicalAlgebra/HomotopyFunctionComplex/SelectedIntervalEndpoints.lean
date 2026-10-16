module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition

/-! # Both entire endpoint systems of the same selected interval diagram -/

@[expose] public section
universe v u uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev baseParameters := SelectedIntervalDiagram.forget C ⋙
  ResolutionArrowComparisonEndpoints.parameter C
abbrev pointParameters := NerveCylinderBoundary.product (baseParameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))
abbrev faceMap (ε : Fin 2) : pointParameters C ⟶ SelectedIntervalDiagram.parameters C :=
  Functor.whiskerLeft (SelectedIntervalDiagram.forget C) (NerveCylinderBoundary.vertical
    (SSet.stdSimplex.δ ε) (ResolutionArrowComparisonEndpoints.parameter C))

abbrev left : NerveMovingParameter.System.{u, v} (baseParameters C)
    (SelectedIntervalDiagram.smallValues C) :=
  reindex _ _ (SelectedIntervalDiagram.forget C) (ResolutionArrowComparisonEndpoints.left C hcof)
abbrev right : NerveMovingParameter.System.{u, v} (baseParameters C)
    (SelectedIntervalDiagram.smallValues C) :=
  reindex _ _ (SelectedIntervalDiagram.forget C) (ResolutionArrowComparisonEndpoints.right C hcof)

lemma coherent_zero : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
    (pointParameters C) (SelectedIntervalDiagram.parameters C)
      (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) (faceMap C 1) =
    NerveProductParameter.expand (baseParameters C)
      (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (left C hcof) := by
  have hb : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
      (SelectedIntervalDiagram.boundaries C) (SelectedIntervalDiagram.parameters C)
        (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
          (SelectedIntervalDiagram.boundaryInclusion C) =
      SelectedIntervalDiagram.fixedBoundary C hcof :=
    SelectedIntervalDiagram.coherent_boundary C hcof hfib
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (1 : Fin 2))
        (ResolutionArrowComparisonEndpoints.parameter C))) = _
  rw [← ResolutionArrowCylinderFaces.zero]
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (ResolutionArrowCylinderBoundary.zeroInclusion C) ≫
        SelectedIntervalDiagram.boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, hb]
  change reindex _ _ (SelectedIntervalDiagram.forget C)
    (ResolutionArrowCylinderBoundary.system C hcof) ≫ restriction _ _ _
      (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
        (ResolutionArrowCylinderBoundary.zeroInclusion C)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_zero, reindex_expand]
  rfl

lemma coherent_one : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
    (pointParameters C) (SelectedIntervalDiagram.parameters C)
      (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) (faceMap C 0) =
    NerveProductParameter.expand (baseParameters C)
      (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (right C hcof) := by
  have hb : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
      (SelectedIntervalDiagram.boundaries C) (SelectedIntervalDiagram.parameters C)
        (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
          (SelectedIntervalDiagram.boundaryInclusion C) =
      SelectedIntervalDiagram.fixedBoundary C hcof :=
    SelectedIntervalDiagram.coherent_boundary C hcof hfib
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (0 : Fin 2))
        (ResolutionArrowComparisonEndpoints.parameter C))) = _
  rw [← ResolutionArrowCylinderFaces.one]
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (ResolutionArrowCylinderBoundary.oneInclusion C) ≫
        SelectedIntervalDiagram.boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, hb]
  change reindex _ _ (SelectedIntervalDiagram.forget C)
    (ResolutionArrowCylinderBoundary.system C hcof) ≫ restriction _ _ _
      (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
        (ResolutionArrowCylinderBoundary.oneInclusion C)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_one, reindex_expand]
  rfl

variable {E : Type uE} [Category.{vE} E] (B : E ⥤ SelectedIntervalDiagram.Index C)

lemma reindex_left : reindex (baseParameters C)
    (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B (left C hcof) =
    NerveArrowComparisonComposition.leftAlong (ResolutionArrowTupleCoherence.bigTuples C)
      (NerveMovingParameter.lifted (ResolutionArrowDiagram.fibers C))
      (ResolutionArrowTupleCoherence.system C hcof)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.leftFunc)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.rightFunc)
      (Functor.whiskerLeft (B ⋙ SelectedIntervalDiagram.forget C) Arrow.leftToRight) := by
  change reindex _ _ B (reindex _ _ (SelectedIntervalDiagram.forget C)
    (NerveArrowComparison.left _ _ (ResolutionArrowTupleCoherence.system C hcof))) = _
  rw [reindex_reindex, NerveArrowComparisonComposition.left_reindex]

lemma reindex_right : reindex (baseParameters C)
    (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B (right C hcof) =
    NerveArrowComparisonComposition.rightAlong (ResolutionArrowTupleCoherence.bigTuples C)
      (NerveMovingParameter.lifted (ResolutionArrowDiagram.fibers C))
      (ResolutionArrowTupleCoherence.system C hcof)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.leftFunc)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.rightFunc)
      (Functor.whiskerLeft (B ⋙ SelectedIntervalDiagram.forget C) Arrow.leftToRight) := by
  change reindex _ _ B (reindex _ _ (SelectedIntervalDiagram.forget C)
    (NerveArrowComparison.right _ _ (ResolutionArrowTupleCoherence.system C hcof))) = _
  rw [reindex_reindex, NerveArrowComparisonComposition.right_reindex]

lemma reindexed_zero : reindex (SelectedIntervalDiagram.parameters C)
    (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
      (SelectedIntervalDiagram.coherent C hcof hfib) ≫ restriction _ _ _
        (Functor.whiskerLeft B (faceMap C 1)) =
    NerveProductParameter.expand (B ⋙ baseParameters C)
      (B ⋙ NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0))
          (reindex (baseParameters C)
            (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
              (left C hcof)) := by
  rw [← reindex_restriction, coherent_zero, reindex_expand]

lemma reindexed_one : reindex (SelectedIntervalDiagram.parameters C)
    (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
      (SelectedIntervalDiagram.coherent C hcof hfib) ≫ restriction _ _ _
        (Functor.whiskerLeft B (faceMap C 0)) =
    NerveProductParameter.expand (B ⋙ baseParameters C)
      (B ⋙ NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0))
          (reindex (baseParameters C)
            (NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
              (right C hcof)) := by
  rw [← reindex_restriction, coherent_one, reindex_expand]

end SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints
