module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedFiberTransportNaturality
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices

/-!
概要：元の辺を左 Hom の指定頂点にし、全左 Hom の普遍輸送で元の辺輸送を回収する。
方針：coslice の頂点全単射と全輸送族の比較を使う。
規約：元の辺の代表を保持。使われ方：余錐の全 Hom の像での Kan 射の識別。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の辺を、同じ端点を持つ左 pinched Hom の頂点として表示する。 -/
def leftHomEdgePoint {X : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    (pinchedHomLeft a b) _⦋0⦌ :=
  (pinchedLeftCosliceFiberIso a b).inv.app (Opposite.op ⦋0⦌)
    ((cosliceFiberVertexEquiv a b).symm e)

/-- 左 Hom の元の辺の頂点は、区間比較でも同じ元の辺の区間頂点になる。 -/
lemma leftHomEdgePoint_interval {X : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    (pinchedHomLeftToIntervalMappingSpace a b).app (Opposite.op ⦋0⦌) (leftHomEdgePoint e) =
      intervalMappingVertexOfEdge e := by
  change (cosliceFiberToIntervalMappingSpace a b).app _
    ((pinchedLeftCosliceFiberIso a b).hom.app _
      ((pinchedLeftCosliceFiberIso a b).inv.app _ ((cosliceFiberVertexEquiv a b).symm e))) = _
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pinchedLeftCosliceFiberIso a b).inv_hom_id (Opposite.op ⦋0⦌))
      ((cosliceFiberVertexEquiv a b).symm e)
  change (pinchedLeftCosliceFiberIso a b).hom.app _
    ((pinchedLeftCosliceFiberIso a b).inv.app _ ((cosliceFiberVertexEquiv a b).symm e)) = _ at h
  rw [h]
  rw [cosliceFiberToIntervalMappingSpace_vertex]
  exact congrArg intervalMappingVertexOfEdge ((cosliceFiberVertexEquiv a b).apply_symm_apply e)

/-- 全左 Hom の元の輸送を指定辺で評価すると、同じ辺の元の輸送射の関手頂点と同型。 -/
def pointedLeftHomEdgeTransportIso {a b : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge a b) :
    VertexIso
      ((F2.pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace a b)).map.app
        (Opposite.op ⦋0⦌) (leftHomEdgePoint e))
      (functorVertex (edgeTransport pointedSpaceProjection e)) := by
  let c := pinchedHomLeftToIntervalMappingSpace a b
  let T := F2.pointedIntervalTransport c
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry c)
      (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) = c := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  have h := T.mapIso_parametrized pointedSpaceProjection (intervalMappingUncurry c)
    (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c)
  rw [hc] at h
  have hx := h.app (leftHomEdgePoint e)
  change VertexIso (T.map.app _ (leftHomEdgePoint e))
    ((parametrizedFiberTransport pointedSpaceProjection a b).app _
      (c.app _ (leftHomEdgePoint e))) at hx
  rw [show c.app _ (leftHomEdgePoint e) = intervalMappingVertexOfEdge e
    from leftHomEdgePoint_interval e] at hx
  let g := (functorVertexEquiv _ _).symm
    ((parametrizedFiberTransport pointedSpaceProjection a b).app _
      (intervalMappingVertexOfEdge e))
  have hg : functorVertex g =
      (parametrizedFiberTransport pointedSpaceProjection a b).app _
        (intervalMappingVertexOfEdge e) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  rw [← hg] at hx
  exact hx ≪≫ parametrizedFiberTransport_at_edgeIso pointedSpaceProjection e

end SerrePositivity.InfinityCategories.HomotopyLimits
