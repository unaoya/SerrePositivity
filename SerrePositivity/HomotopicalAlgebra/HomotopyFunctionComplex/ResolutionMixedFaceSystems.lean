module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery

/-! # The actual five whole edge systems form the two compatible mixed triangle boundaries -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedIntervalRestrictions ResolutionMixedEndpointCompatibility

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedFaceSystems
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- Both boundaries use the same four old interval systems and the same old diagonal system. -/
def faces (side : Bool) : Fin 3 →
    NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C) :=
  if side then ![intervalBD C hcof hfib, ResolutionMixedCoherentDiagonal.coherent C hcof hfib,
    intervalAB C hcof hfib]
  else ![intervalCD C hcof hfib, ResolutionMixedCoherentDiagonal.coherent C hcof hfib,
    intervalAC C hcof hfib]

lemma compatible (side : Bool) (j k : Fin 3) (hjk : j < k) :
    endpoint C (faces C hcof hfib side j) (k.pred (Fin.ne_zero_of_lt hjk)) =
      endpoint C (faces C hcof hfib side k) (j.castPred (Fin.ne_last_of_lt hjk)) := by
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · cases side
    · exact (CD_one C hcof hfib).trans (ResolutionMixedCoherentDiagonal.coherent_one C hcof
      hfib).symm
    · exact (BD_one C hcof hfib).trans (ResolutionMixedCoherentDiagonal.coherent_one C hcof
      hfib).symm
  · cases side
    · exact (commonC C hcof hfib).symm
    · exact (commonB C hcof hfib).symm
  · cases side
    · exact (ResolutionMixedCoherentDiagonal.coherent_zero C hcof hfib).trans
        (AC_zero C hcof hfib).symm
    · exact (ResolutionMixedCoherentDiagonal.coherent_zero C hcof hfib).trans
        (AB_zero C hcof hfib).symm

lemma shared_diagonal : faces C hcof hfib true 1 = faces C hcof hfib false 1 := by
  unfold faces
  simp only [Bool.false_eq_true, ite_true, ite_false, Matrix.cons_val_one, Matrix.cons_val_zero]

lemma faces_evaluate (side : Bool) (k : Fin 3) (p : Index C) :
    NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (faces C hcof hfib side k) p = ResolutionMixedTriangles.face C hcof hfib p side k := by
  cases side <;> fin_cases k
  · exact ResolutionMixedEdgeRecovery.intervalCD_face C hcof hfib p
  · exact ResolutionMixedCoherentDiagonal.coherent_evaluate C hcof hfib p
  · exact ResolutionMixedEdgeRecovery.intervalAC_face C hcof hfib p
  · exact ResolutionMixedEdgeRecovery.intervalBD_face C hcof hfib p
  · exact ResolutionMixedCoherentDiagonal.coherent_evaluate C hcof hfib p
  · exact ResolutionMixedEdgeRecovery.intervalAB_face C hcof hfib p

/-- Every old whole triangle evaluates to these fixed whole edge systems along its faces. -/
lemma old_triangle_faces (side : Bool) (k : Fin 3) (p : Index C) :
    (parameters C).obj p ◁ SSet.stdSimplex.δ k ≫ ResolutionMixedTriangles.triangle C hcof hfib p
      side =
    NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (faces C hcof hfib side k) p :=
  (ResolutionMixedTriangles.triangle_face C hcof hfib p side k).trans
    (faces_evaluate C hcof hfib side k p).symm

lemma faces_recover (side : Bool) (k : Fin 3) (p : Index C) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (faces C hcof hfib side k) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p) (ResolutionMixedTriangles.oldFace C hcof hfib p
        side k) :=
  (congrArg UniverseLift.lowerSimplexTensor (faces_evaluate C hcof hfib side k p)).trans
    (ResolutionMixedTriangles.face_recover C hcof hfib p side k)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedFaceSystems
