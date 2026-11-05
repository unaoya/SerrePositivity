module
public import SerrePositivity.KST.Fibration.StraighteningRepresentationRestriction
public import SerrePositivity.KST.Fibration.NativeRepresentationPoint

/-! # pointed 復元の同じ指定点を、元の初頂点制限比較の逆成分で計算する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- 元の復元射の同じ fiber 点は、元の制限比較の同じ逆成分で回収される。 -/
theorem pointedLeftReconstruction_restriction_pointHom (c : TransportSimplexCategory B)
    (v : (vertexFiber p ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
      (nerveVertex c))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
        (Opposite.op ⦋0⦌) (ULift.up v)) ≫
      functorHomEvaluate
        (straighteningRepresentationRestrictionIso p (nativeLeftTransportRepresentation p)).inv
        (ULift.up (nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p)
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction p)
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction_projection p)
        ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
          (Opposite.op ⦋0⦌) v)) := by
  let b := (transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)
  have hp := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction_pointHom p b v
  rw [nativeLeftTransportComparison_pointedImage] at hp
  have hi := leftStraighteningRepresentationIso_inv_value p (nativeLeftTransportRepresentation p) c
  have he := congrArg (fun m => _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
    ((nativeTransportPointedFiberMap p b).app (Opposite.op ⦋0⦌) (ULift.up v)) ≫ m) hi
  exact he.symm.trans hp

end SerrePositivity.KST.Fibration
