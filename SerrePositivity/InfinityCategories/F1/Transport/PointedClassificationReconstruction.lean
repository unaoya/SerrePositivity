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
  nativeLeftTransportComparison p ≫ _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom
    (leftStraighteningInfinityDiagram_representationIso p (nativeLeftTransportRepresentation p)).inv

omit [Quasicategory B] in
/-- 指定成分を保持する同じ復元射は、元の小さい底を厳密に保つ。 -/
theorem pointedLeftStraighteningReconstruction_projection :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction p ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) = p := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection, nativeLeftTransportComparison_projection]

/-- 指定成分を保持する同じ復元射は前合成同値。 -/
theorem pointedLeftStraighteningReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction p) :=
  (nativeLeftTransportComparison_isPrecompositionEquivalence p).comp
    (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_isPrecompositionEquivalence _)

omit [Quasicategory B] in
/-- 復元射による同じ fiber 点の像は、native 表現の点と指定分類同型の逆成分で計算できる。 -/
theorem pointedLeftStraighteningReconstruction_pointHom (b : B _⦋0⦌)
    (v : (vertexFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (nativeLeftTransportRepresentation p).diagram b
      ((vertexFiberMap p
        (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
        (nativeLeftTransportComparison p) (nativeLeftTransportComparison_projection p) b).app
          (Opposite.op ⦋0⦌) v)) ≫
      functorHomEvaluate
        (leftStraighteningInfinityDiagram_representationIso p
          (nativeLeftTransportRepresentation p)).inv (ULift.up b) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram p) b
        ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
          (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction p)
          (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedLeftStraighteningReconstruction_projection p) b).app (Opposite.op ⦋0⦌) v)) := by
  let a := (leftStraighteningInfinityDiagram_representationIso p
    (nativeLeftTransportRepresentation p)).inv
  let w := (vertexFiberMap p
    (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
    (nativeLeftTransportComparison p) (nativeLeftTransportComparison_projection p) b).app
      (Opposite.op ⦋0⦌) v
  have he := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_pointHom a b w
  have hf := vertexFiberMap_comp p
    (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
    (nativeLeftTransportComparison p) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a)
    (nativeLeftTransportComparison_projection p) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection a) b
  have hv := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) hf
  exact he.trans (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
    (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram p) b z)) hv)

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
