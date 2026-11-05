module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningPointHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction

/-! # 同じ指定分類成分による実点の作用を保持した、小さい left fibration の復元 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration
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
    _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection, nativeLeftTransportComparison_projection]

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

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedLeftStraighteningReconstruction := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedLeftStraighteningReconstruction_isPrecompositionEquivalence := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction_isPrecompositionEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedLeftStraighteningReconstruction_pointHom := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction_pointHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedLeftStraighteningReconstruction_projection := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedLeftStraighteningReconstruction.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction.eq_1
