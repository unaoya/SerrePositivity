module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProductProjectionFiber

/-!
概要：点ごとの積の元の全空間作用は、各 pointed fiber で二つの fiber の積への同値。
方針：選択済み変換の作用を普遍輸送へ比較し、同じ二射影辺を一点で回収する。
規約：底の quasicategory 性や変換の可逆性を要求しない。
使われ方：元の小さい全空間の引き戻し比較の fiber 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration kanTensor_isKan
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)

/-- 元の両変換の全空間作用を各 pointed fiber に制限した二射影の対。 -/
def coherentProductPointedFiberMap :
    vertexFiber pointedSpaceProjection
        ((coherentSpaceTensorProduct F G).app (Opposite.op ⦋0⦌) (ULift.up b)) ⟶
      vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) (ULift.up b)) ⊗
        vertexFiber pointedSpaceProjection (G.app (Opposite.op ⦋0⦌) (ULift.up b)) :=
  lift
    (leftUnstraighteningPointedFiberMap _ _
      (leftUnstraighteningMappingVertexMap _ _ (coherentSpaceTensorProductFstVertex F G)).val
      (leftUnstraighteningMappingVertexMap _ _ (coherentSpaceTensorProductFstVertex F G)).property
      (ULift.up b))
    (leftUnstraighteningPointedFiberMap _ _
      (leftUnstraighteningMappingVertexMap _ _ (coherentSpaceTensorProductSndVertex F G)).val
      (leftUnstraighteningMappingVertexMap _ _ (coherentSpaceTensorProductSndVertex F G)).property
      (ULift.up b))

/-- 指定済みの全空間作用の fiber と、同じ二射影の普遍輸送の対は関手同型。 -/
def coherentProductPointedFiberTransportIso :
    FunctorIso (coherentProductPointedFiberMap F G b)
      (spaceTensorProductFiberTransport (F.app _ (ULift.up b)) (G.app _ (ULift.up b))) := by
  have e := pairedKanFunctorIso
    (leftUnstraighteningMappingVertex_pointedFiberTransportIso _ _
      (coherentSpaceTensorProductFstVertex F G) (ULift.up b))
    (leftUnstraighteningMappingVertex_pointedFiberTransportIso _ _
      (coherentSpaceTensorProductSndVertex F G) (ULift.up b))
  have he : functorEdgeAt
      (intervalMappingEdgeOfVertex (coherentSpaceTensorProductFstVertex F G)) (ULift.up b) =
        simplicialHomotopyVertexEdge spaceTensorProductFstHomotopy
          (F.app _ (ULift.up b), G.app _ (ULift.up b)) := by
    apply SSet.Edge.ext
    exact coherentSpaceTensorProductFstVertex_edgeAt F G b
  have hf : functorEdgeAt
      (intervalMappingEdgeOfVertex (coherentSpaceTensorProductSndVertex F G)) (ULift.up b) =
        simplicialHomotopyVertexEdge spaceTensorProductSndHomotopy
          (F.app _ (ULift.up b), G.app _ (ULift.up b)) := by
    apply SSet.Edge.ext
    exact coherentSpaceTensorProductSndVertex_edgeAt F G b
  rw [he, hf] at e
  exact e

/-- 各 pointed fiber で、元の全空間の二つの射影作用の対は同値。 -/
lemma coherentProductPointedFiberMap_isQCatEquivalence :
    IsQCatEquivalence (coherentProductPointedFiberMap F G b) :=
  (spaceTensorProductFiberTransport_isQCatEquivalence _ _).ofFunctorIso
    (coherentProductPointedFiberTransportIso F G b).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
