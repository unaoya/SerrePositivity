module
public import SerrePositivity.InfinityCategories.F1.Transport.PointedClassificationReconstruction
public import SerrePositivity.InfinityCategories.F1.Transport.CoslicePointComparison

/-! # 指定成分の作用を保持する復元射の、同じ coslice 恒等点における値 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 恒等錐での正規化済み評価は、同じ実 coslice fiber の恒等点の像そのもの。 -/
theorem coslicePointEvaluation_fiberMap_identity {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (f : sliceUnder (yonedaEquiv.symm b) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (yonedaEquiv.symm b)) :
    (leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex p _ f hf) =
      (vertexFiberMap (sliceUnderProjection (yonedaEquiv.symm b)) p f hf b).app
        (Opposite.op ⦋0⦌) (edgeToCosliceFiberVertex (SSet.Edge.id b)) := by
  apply Subtype.ext
  have hi : (edgeToCosliceFiberVertex (SSet.Edge.id b)).val = cosliceIdentityCone b := by
    apply Subtype.ext
    change (joinStdSimplexIso 0 0).hom ≫ yonedaEquiv.symm (B.σ 0 b) = SSet.const b
    rw [← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero,
      SSet.comp_const, SSet.comp_const]
  have hm := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (edgeToCosliceFiberVertex (SSet.Edge.id b)))
    (vertexFiberMap_ι (sliceUnderProjection (yonedaEquiv.symm b)) p f hf b)
  change _ = f.app (Opposite.op ⦋0⦌) (edgeToCosliceFiberVertex (SSet.Edge.id b)).val at hm
  rw [hi] at hm
  exact (coslicePointEvaluation_vertex_val p b hf).trans hm.symm

variable {B : SSet.{u}} [Quasicategory B] (b : B _⦋0⦌)

/-- 同じ分類成分の作用を保持する復元射の、元の coslice 恒等錐での実 fiber 点。 -/
def pointedCosliceReconstructionPoint :
    (vertexFiber (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm b)))) b) _⦋0⦌ :=
  (leftFibrationCoslicePointEvaluate _ b).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ (pointedLeftStraighteningReconstruction
      (sliceUnderProjection (yonedaEquiv.symm b)))
      (pointedLeftStraighteningReconstruction_projection _))

/-- 復元写像の同じ指定点は、元の coslice 恒等点の実 fiber 写像による像。 -/
theorem pointedCosliceReconstructionPoint_fiberMap :
    pointedCosliceReconstructionPoint b =
      (vertexFiberMap (sliceUnderProjection (yonedaEquiv.symm b))
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm b))))
        (pointedLeftStraighteningReconstruction (sliceUnderProjection (yonedaEquiv.symm b)))
        (pointedLeftStraighteningReconstruction_projection _) b).app (Opposite.op ⦋0⦌)
          (edgeToCosliceFiberVertex (SSet.Edge.id b)) :=
  coslicePointEvaluation_fiberMap_identity _ b _ _

/-- 指定復元点の射は、native 表現による恒等点の像と、同じ分類同型の逆成分との合成。 -/
theorem pointedCosliceReconstructionPoint_pointHom :
    cosliceFiberPointHom (smallUnstraighteningPointedImage
      (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b))).diagram b
      ((vertexFiberMap (sliceUnderProjection (yonedaEquiv.symm b))
        (smallLeftUnstraighteningProjection
          (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b))).diagram)
        (nativeLeftTransportComparison (sliceUnderProjection (yonedaEquiv.symm b)))
        (nativeLeftTransportComparison_projection _) b).app (Opposite.op ⦋0⦌)
          (edgeToCosliceFiberVertex (SSet.Edge.id b)))) ≫
      functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso
        (sliceUnderProjection (yonedaEquiv.symm b))
        (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b)))).inv
          (ULift.up b) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram (sliceUnderProjection (yonedaEquiv.symm b))) b
        (pointedCosliceReconstructionPoint b)) := by
  rw [pointedCosliceReconstructionPoint_fiberMap]
  exact pointedLeftStraighteningReconstruction_pointHom _ b _

end SerrePositivity.KST.Fibration
