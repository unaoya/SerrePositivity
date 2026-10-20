module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofIdentityRefinement
/-!
概要：指定閉分母から恒等分母への実細分辺を、閉分母そのものを始点として構成する。
方針：同じ実閉辺の退化合成三角形を slice に移し、全部分複体に持ち上げる。
規約：元の分母の一次単体を厳密に保持する。使われ方：評価族の実屋根比較の底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 指定閉分母から恒等分母への、同じ実閉辺の上にある実細分辺。 -/
def dgClosedDenominatorIdentityEdge (P : Set D) (x : D)
    (r : DGClosedVerdierDenominators A D P x) :
    Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet))
      (dgClosedVerdierDenominatorVertex A D P x r) (dgVerdierOverIdentityVertex A D P x) :=
  fullSubcomplexEdgeLift (IsDGVerdierOverVertex A D P x)
    (dgClosedVerdierDenominatorVertex A D P x r) (dgVerdierOverIdentityVertex A D P x)
    (roofPointSliceCompositionEdge (X := dgNerve A D)
      (Truncated.Edge.CompStruct.compId (dgClosedEdge A D r.obj.hom))).edge
    ((roofPointSliceCompositionEdge (X := dgNerve A D)
      (Truncated.Edge.CompStruct.compId (dgClosedEdge A D r.obj.hom))).src_eq.trans
        (roofPointSliceEdgeVertex_vertex (dgClosedEdge A D r.obj.hom)
          (dgClosedOverVertex A D r.obj.hom) (dgClosedOverVertex_edge A D r.obj.hom).symm))
    ((roofPointSliceCompositionEdge (X := dgNerve A D)
      (Truncated.Edge.CompStruct.compId (dgClosedEdge A D r.obj.hom))).tgt_eq.trans
        (roofPointSliceEdgeVertex_id (X := dgNerve A D) (Simplex.vertex x)))
/-- 実細分辺の始域への射影は、元の指定閉分母の実辺。 -/
lemma dgClosedDenominatorIdentityEdge_source (P : Set D) (x : D)
    (r : DGClosedVerdierDenominators A D P x) :
    (dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      (dgClosedDenominatorIdentityEdge A D P x r).edge = (dgClosedEdge A D r.obj.hom).edge := by
  exact roofPointSliceCompositionEdge_projection (X := dgNerve A D)
    (Truncated.Edge.CompStruct.compId (dgClosedEdge A D r.obj.hom))
end SerrePositivity.InfinityCategories
