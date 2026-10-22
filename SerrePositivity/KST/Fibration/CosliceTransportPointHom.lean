module
public import SerrePositivity.KST.Fibration.CosliceEdgeComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeTransportPointLift

/-! # 元の coslice fiber 点の輸送は、同じ点の矢印と底の辺の合成を表す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration

/-- 元の coslice fiber 点の、指定した始点から終点への実際の矢印の類。 -/
def cosliceFiberPointHom {X : SSet.{u}} {x a : X _⦋0⦌}
    (v : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a) _⦋0⦌) :
    HomotopyCategory.mk x ⟶ HomotopyCategory.mk a :=
  Truncated.HomotopyCategory.homMk (cosliceFiberVertexToEdge v).toTruncated

/-- 指定された実 transport の点の像は、元の点の矢印と指定された底の辺の合成を表す。 -/
theorem cosliceTransportPointHom {X : SSet.{u}} {x a b : X _⦋0⦌}
    (e : X.Edge a b)
    (F : vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a ⟶
      vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) b)
    (hF : IsEdgeTransport (sliceUnderProjection (yonedaEquiv.symm x)) e F)
    (v : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a) _⦋0⦌) :
    cosliceFiberPointHom v ≫ Truncated.HomotopyCategory.homMk e.toTruncated =
      cosliceFiberPointHom (F.app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨l, hl⟩ := exists_edge_of_transport_point _ e F hF v
  have hb : cosliceFiberBaseEdge v (F.app (Opposite.op ⦋0⦌) v) l = e := SSet.Edge.ext hl
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk
    (cosliceFiberEdgeCompStruct v (F.app (Opposite.op ⦋0⦌) v) l).toTruncated
  rw [hb] at hc
  exact hc

/-- 同じ実 coslice fiber 内の辺は、元の始点からの矢印の類を保持する。 -/
theorem cosliceFiberPointHom_eq_of_edge {X : SSet.{u}} {x a : X _⦋0⦌}
    {v w : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a) _⦋0⦌}
    (l : SSet.Edge v w) : cosliceFiberPointHom v = cosliceFiberPointHom w := by
  let p := sliceUnderProjection (yonedaEquiv.symm x)
  let k := l.map (vertexFiberι p a)
  have hb : cosliceFiberBaseEdge v w k = SSet.Edge.id a := by
    apply SSet.Edge.ext
    have he := congrArg (fun m => m.app (Opposite.op ⦋1⦌) l.edge) (vertexFiberι_comp p a)
    exact he.trans (pinchedConstant_one a)
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk
    (cosliceFiberEdgeCompStruct v w k).toTruncated
  rw [hb, SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id,
    Category.comp_id] at hc
  exact hc

/-- 同じ実 fiber 内の頂点同型も、指定された元の矢印の類を保持する。 -/
theorem cosliceFiberPointHom_eq_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x a : X _⦋0⦌}
    {v w : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a) _⦋0⦌}
    (e : VertexIso v w) : cosliceFiberPointHom v = cosliceFiberPointHom w := by
  have := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (yonedaEquiv.symm x)) a
  obtain ⟨l, _⟩ := homotopyCategory_homMk_surjective v w e.hom
  exact cosliceFiberPointHom_eq_of_edge (SSet.Edge.ofTruncated l)

end SerrePositivity.KST.Fibration
