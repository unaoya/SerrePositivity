module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociationEquality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport

/-! # Exact whole endpoints before the final mixed parameter and value transports -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation ResolutionMixedIntervalRestrictions
open NerveBiparameterMaps NerveArrowComparisonComposition

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev K := ResolutionArrowTupleCoherence.bigTuples C
abbrev F := NerveMovingParameter.lifted.{u} (ResolutionArrowDiagram.fibers C)
abbrev chosen := ResolutionArrowTupleCoherence.system C hcof

abbrev leftAB := leftAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerB C) (edgeAB C)

abbrev rightAB := rightAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerB C) (edgeAB C)

lemma AB_zero : preABSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (NerveMovingParameter.lifted (bValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (NerveMovingParameter.lifted (bValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftAB C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (preAB C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (NerveMovingParameter.lifted (bValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_left C hcof (preAB C))

lemma AB_one : preABSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (NerveMovingParameter.lifted (bValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (NerveMovingParameter.lifted (bValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightAB C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (preAB C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (NerveMovingParameter.lifted (bValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_right C hcof (preAB C))

abbrev leftAC := leftAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (edgeAC C)

abbrev rightAC := rightAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (edgeAC C)

lemma AC_zero : postACSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (NerveMovingParameter.lifted (cValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (NerveMovingParameter.lifted (cValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftAC C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (postAC C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (NerveMovingParameter.lifted (cValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_left C hcof (postAC C))

lemma AC_one : postACSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (NerveMovingParameter.lifted (cValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (NerveMovingParameter.lifted (cValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightAC C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (postAC C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (NerveMovingParameter.lifted (cValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_right C hcof (postAC C))

abbrev leftCD := leftAlong (K C) (F C) (chosen C hcof) (cornerC C) (cornerD C) (edgeCD C)

abbrev rightCD := rightAlong (K C) (F C) (chosen C hcof) (cornerC C) (cornerD C) (edgeCD C)

lemma CD_zero : preCDSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (cParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (cIntervalParameters C)
    (NerveMovingParameter.lifted (smallValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (cParameters C)) =
    NerveProductParameter.expand (cParameters C) (NerveMovingParameter.lifted (smallValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftCD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (preCD C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (cParameters C)
    (NerveMovingParameter.lifted (smallValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_left C hcof (preCD C))

lemma CD_one : preCDSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (cParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (cIntervalParameters C)
    (NerveMovingParameter.lifted (smallValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (cParameters C)) =
    NerveProductParameter.expand (cParameters C) (NerveMovingParameter.lifted (smallValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightCD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (preCD C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (cParameters C)
    (NerveMovingParameter.lifted (smallValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_right C hcof (preCD C))

abbrev leftBD := leftAlong (K C) (F C) (chosen C hcof) (cornerB C) (finalLeft C) (edgeBDLeft C)

abbrev rightBD := rightAlong (K C) (F C) (chosen C hcof) (cornerB C) (finalLeft C) (edgeBDLeft C)

lemma BD_zero : postBDSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (bParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (bIntervalParameters C)
    (NerveMovingParameter.lifted (leftFinalValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (bParameters C)) =
    NerveProductParameter.expand (bParameters C) (NerveMovingParameter.lifted (leftFinalValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftBD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (postBD C)).trans
  have hτ : Functor.whiskerLeft (postBD C ⋙ SelectedIntervalDiagram.forget C)
      Arrow.leftToRight = edgeBDLeft C := by
    apply NatTrans.ext
    funext p
    exact (edgeBDLeft_app C p).symm
  have he := SelectedIntervalEndpoints.reindex_left C hcof (postBD C)
  rw [hτ] at he
  exact congrArg (fun a => NerveProductParameter.expand (bParameters C)
    (NerveMovingParameter.lifted (leftFinalValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk
      0)) a) he

lemma BD_one : postBDSystem C hcof hfib ≫ restriction
    (NerveCylinderBoundary.product (bParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (bIntervalParameters C)
    (NerveMovingParameter.lifted (leftFinalValues C))
      (NerveCylinderBoundary.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (bParameters C)) =
    NerveProductParameter.expand (bParameters C) (NerveMovingParameter.lifted (leftFinalValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightBD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (postBD C)).trans
  have hτ : Functor.whiskerLeft (postBD C ⋙ SelectedIntervalDiagram.forget C)
      Arrow.leftToRight = edgeBDLeft C := by
    apply NatTrans.ext
    funext p
    exact (edgeBDLeft_app C p).symm
  have he := SelectedIntervalEndpoints.reindex_right C hcof (postBD C)
  rw [hτ] at he
  exact congrArg (fun a => NerveProductParameter.expand (bParameters C)
    (NerveMovingParameter.lifted (leftFinalValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk
      0)) a) he

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints
