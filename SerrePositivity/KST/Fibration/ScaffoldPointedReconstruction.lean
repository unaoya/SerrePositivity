module
public import SerrePositivity.KST.Fibration.ScaffoldStraighteningComparison
public import SerrePositivity.InfinityCategories.F1.Transport.PointedClassificationReconstruction

/-! # 指定 scaffold 制限比較を用いる小さい left fibration の復元

指定した分類成分を実写像に使い、射影と元の fiber 点の作用を保持する。
係数点との最終照合は、この比較の元の制限三角形から別途証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- 指定 scaffold 三角形を保持する分類比較の同じ逆成分を使う実復元射。 -/
def scaffoldPointedReconstruction :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram p) :=
  nativeLeftTransportComparison p ≫ _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom
    (scaffoldStraighteningRepresentationIso p (nativeLeftTransportRepresentation p)).inv

/-- 元の底への射影は厳密に回収する。 -/
theorem scaffoldPointedReconstruction_projection :
    scaffoldPointedReconstruction p ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) = p := by
  rw [scaffoldPointedReconstruction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection, nativeLeftTransportComparison_projection]

/-- 同じ実復元射は、元の底上の前合成同値である。 -/
theorem scaffoldPointedReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (scaffoldPointedReconstruction p) :=
  (nativeLeftTransportComparison_isPrecompositionEquivalence p).comp
    (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_isPrecompositionEquivalence _)

/-- 元の実 fiber 点の像は、指定した同じ分類逆成分の作用で計算できる。 -/
theorem scaffoldPointedReconstruction_pointHom (b : B _⦋0⦌)
    (v : (vertexFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (nativeLeftTransportRepresentation p).diagram b
      ((vertexFiberMap p
        (smallLeftUnstraighteningProjection (nativeLeftTransportRepresentation p).diagram)
        (nativeLeftTransportComparison p) (nativeLeftTransportComparison_projection p) b).app
          (Opposite.op ⦋0⦌) v)) ≫
      functorHomEvaluate
        (scaffoldStraighteningRepresentationIso p (nativeLeftTransportRepresentation p)).inv
        (ULift.up b) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p) b
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p) (scaffoldPointedReconstruction_projection p) b).app
          (Opposite.op ⦋0⦌) v)) := by
  let a := (scaffoldStraighteningRepresentationIso p (nativeLeftTransportRepresentation p)).inv
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

end SerrePositivity.KST.Fibration
