module
public import SerrePositivity.KST.Fibration.NativeRepresentationPoint
public import SerrePositivity.KST.Fibration.PointedCosliceReconstruction

/-! # 同じ coslice 恒等点の native 表現と、指定復元点の射との比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}} [Quasicategory B] (b : B _⦋0⦌)

/-- 元の coslice 恒等点を同じ native 表現の pointedMap で送った実 fiber 点。 -/
def nativeCosliceIdentityPoint :
    (vertexFiber pointedSpaceProjection
      ((nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b))).diagram.app
        (Opposite.op ⦋0⦌) (ULift.up b))) _⦋0⦌ :=
  (nativeTransportPointedFiberMap (sliceUnderProjection (yonedaEquiv.symm b)) b).app
    (Opposite.op ⦋0⦌) (ULift.up (edgeToCosliceFiberVertex (SSet.Edge.id b)))

/-- 元の native 比較の恒等点像は、同じ pointedMap による指定点そのもの。 -/
theorem nativeCosliceIdentityPoint_eq_comparison :
    smallUnstraighteningPointedImage
      (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b))).diagram b
      ((vertexFiberMap (sliceUnderProjection (yonedaEquiv.symm b))
        (smallLeftUnstraighteningProjection
          (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b))).diagram)
        (nativeLeftTransportComparison (sliceUnderProjection (yonedaEquiv.symm b)))
        (nativeLeftTransportComparison_projection _) b).app (Opposite.op ⦋0⦌)
          (edgeToCosliceFiberVertex (SSet.Edge.id b))) = nativeCosliceIdentityPoint b :=
  nativeLeftTransportComparison_pointedImage _ b _

/-- 指定復元点の射は、元の native 恒等点と同じ分類成分の逆射で厳密に計算できる。 -/
theorem pointedCosliceReconstructionPoint_native_pointHom :
    cosliceFiberPointHom (nativeCosliceIdentityPoint b) ≫
      functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso
        (sliceUnderProjection (yonedaEquiv.symm b))
        (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b)))).inv
          (ULift.up b) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram (sliceUnderProjection (yonedaEquiv.symm b))) b
        (pointedCosliceReconstructionPoint b)) := by
  have he := pointedCosliceReconstructionPoint_pointHom b
  rw [nativeCosliceIdentityPoint_eq_comparison b] at he
  exact he

end SerrePositivity.KST.Fibration
