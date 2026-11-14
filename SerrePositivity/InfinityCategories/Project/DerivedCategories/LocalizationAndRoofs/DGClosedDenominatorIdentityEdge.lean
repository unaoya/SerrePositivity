module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofIdentityRefinement
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 指定閉分母から恒等分母への、同じ実閉辺の上にある実細分辺。 -/
def dgClosedDenominatorIdentityEdge (P : Set D) (x : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexEdgeLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
      (Truncated.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.obj.hom))).edge
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
      (Truncated.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.obj.hom))).src_eq.trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.obj.hom)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D r.obj.hom) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D r.obj.hom).symm))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
      (Truncated.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.obj.hom))).tgt_eq.trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
/-- 実細分辺の始域への射影は、元の指定閉分母の実辺。 -/
lemma dgClosedDenominatorIdentityEdge_source (P : Set D) (x : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      (dgClosedDenominatorIdentityEdge A D P x r).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.obj.hom).edge := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge_projection (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (Truncated.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.obj.hom))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
