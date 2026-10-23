module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTensorProductTotalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTensorProductFiberTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingFiberTransport

/-!
概要：点ごとの coherent 積の指定変換を一点で評価し、元の二射影辺を回収する。
方針：区間模型の頂点と辺の往復を消し、同じ円柱の底変換を計算する。
規約：底は任意。使われ方：選択済み全空間作用の fiber と元の積輸送との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 第一射影の元の変換頂点の一点評価は、積関手の同じ第一射影辺。 -/
lemma coherentSpaceTensorProductFstVertex_edgeAt (b : B _⦋0⦌) :
    (functorEdgeAt (intervalMappingEdgeOfVertex (coherentSpaceTensorProductFstVertex F G))
      (ULift.up b)).edge =
        (simplicialHomotopyVertexEdge spaceTensorProductFstHomotopy
          (F.app _ (ULift.up b), G.app _ (ULift.up b))).edge := by
  let H := coherentSpaceTensorProductFstHomotopy F G
  let e : SSet.Edge (functorVertex (coherentSpaceTensorProduct F G)) (functorVertex F) :=
    ⟨(functorEdgeOfSimplicialHomotopy H).edge,
      (functorEdgeOfSimplicialHomotopy H).src_eq,
      (functorEdgeOfSimplicialHomotopy H).tgt_eq⟩
  have he : intervalMappingEdgeOfVertex (coherentSpaceTensorProductFstVertex F G) = e :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e
  rw [he]
  change (evaluateFunctorAt (ULift.up b)).app (Opposite.op ⦋1⦌)
    (functorEdgeOfSimplicialHomotopy H).edge = _
  rw [← evaluateFunctorAt_edge, simplicialHomotopyOfFunctorEdge_of_homotopy]
  have hc := pinchedConstant_map (lift F G) (ULift.up b) 1
  rw [pinchedConstant_one, pinchedConstant_one] at hc
  change spaceTensorProductFstHomotopy.h.app (Opposite.op ⦋1⦌)
    ((lift F G).app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj B)) (ULift.up b)).edge,
        homotopyIntervalEdge.edge) = _
  rw [hc]
  rfl

/-- 第二射影の元の変換頂点の一点評価も、積関手の同じ第二射影辺。 -/
lemma coherentSpaceTensorProductSndVertex_edgeAt (b : B _⦋0⦌) :
    (functorEdgeAt (intervalMappingEdgeOfVertex (coherentSpaceTensorProductSndVertex F G))
      (ULift.up b)).edge =
        (simplicialHomotopyVertexEdge spaceTensorProductSndHomotopy
          (F.app _ (ULift.up b), G.app _ (ULift.up b))).edge := by
  let H := coherentSpaceTensorProductSndHomotopy F G
  let e : SSet.Edge (functorVertex (coherentSpaceTensorProduct F G)) (functorVertex G) :=
    ⟨(functorEdgeOfSimplicialHomotopy H).edge,
      (functorEdgeOfSimplicialHomotopy H).src_eq,
      (functorEdgeOfSimplicialHomotopy H).tgt_eq⟩
  have he : intervalMappingEdgeOfVertex (coherentSpaceTensorProductSndVertex F G) = e :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e
  rw [he]
  change (evaluateFunctorAt (ULift.up b)).app (Opposite.op ⦋1⦌)
    (functorEdgeOfSimplicialHomotopy H).edge = _
  rw [← evaluateFunctorAt_edge, simplicialHomotopyOfFunctorEdge_of_homotopy]
  have hc := pinchedConstant_map (lift F G) (ULift.up b) 1
  rw [pinchedConstant_one, pinchedConstant_one] at hc
  change spaceTensorProductSndHomotopy.h.app (Opposite.op ⦋1⦌)
    ((lift F G).app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj B)) (ULift.up b)).edge,
        homotopyIntervalEdge.edge) = _
  rw [hc]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
