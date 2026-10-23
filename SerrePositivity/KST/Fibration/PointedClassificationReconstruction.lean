module
public import SerrePositivity.KST.Fibration.SmallUnstraighteningIsoHom
public import SerrePositivity.KST.Fibration.SmallUnstraighteningPointHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction

/-! # 同じ指定分類成分による実点の作用を保持した、小さい left fibration の復元 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- native 表現から同じ指定分類同型の逆成分を使う復元射。全写像空間の実作用を保持する。 -/
def pointedLeftStraighteningReconstruction :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram p) :=
  nativeLeftTransportComparison p ≫ smallUnstraighteningFunctorHom
    (leftStraighteningInfinityDiagram_representationIso p (nativeLeftTransportRepresentation p)).inv

omit [Quasicategory B] in
/-- 指定成分を保持する同じ復元射は、元の小さい底を厳密に保つ。 -/
theorem pointedLeftStraighteningReconstruction_projection :
    pointedLeftStraighteningReconstruction p ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) = p := by
  rw [pointedLeftStraighteningReconstruction, Category.assoc,
    smallUnstraighteningFunctorHom_projection, nativeLeftTransportComparison_projection]

/-- 指定成分を保持する同じ復元射は前合成同値。 -/
theorem pointedLeftStraighteningReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (pointedLeftStraighteningReconstruction p) :=
  (nativeLeftTransportComparison_isPrecompositionEquivalence p).comp
    (smallUnstraighteningFunctorHom_isPrecompositionEquivalence _)

omit [Quasicategory B] in
/-- 復元射による同じ fiber 点の像は、native 表現の点と指定分類同型の逆成分で計算できる。 -/
theorem pointedLeftStraighteningReconstruction_pointHom (b : B _⦋0⦌)
    (v : (vertexFiber p b) _⦋0⦌) :
    cosliceFiberPointHom (smallUnstraighteningPointedImage
      (nativeLeftTransportRepresentation p).diagram b
      ((vertexFiberMap p
        (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
        (nativeLeftTransportComparison p) (nativeLeftTransportComparison_projection p) b).app
          (Opposite.op ⦋0⦌) v)) ≫
      functorHomEvaluate
        (leftStraighteningInfinityDiagram_representationIso p
          (nativeLeftTransportRepresentation p)).inv (ULift.up b) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram p) b
        ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
          (pointedLeftStraighteningReconstruction p)
          (pointedLeftStraighteningReconstruction_projection p) b).app (Opposite.op ⦋0⦌) v)) := by
  let a := (leftStraighteningInfinityDiagram_representationIso p
    (nativeLeftTransportRepresentation p)).inv
  let w := (vertexFiberMap p
    (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
    (nativeLeftTransportComparison p) (nativeLeftTransportComparison_projection p) b).app
      (Opposite.op ⦋0⦌) v
  have he := smallUnstraighteningFunctorHom_pointHom a b w
  have hf := vertexFiberMap_comp p
    (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
    (nativeLeftTransportComparison p) (smallUnstraighteningFunctorHom a)
    (nativeLeftTransportComparison_projection p) (smallUnstraighteningFunctorHom_projection a) b
  have hv := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) hf
  exact he.trans (congrArg (fun z => cosliceFiberPointHom
    (smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram p) b z)) hv)

end SerrePositivity.KST.Fibration
