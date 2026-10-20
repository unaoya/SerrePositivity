module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofSpans
public import SerrePositivity.InfinityCategories.Derived.RoofPointSliceTriangleEdge
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.Derived.FullSubcomplexEdgeLift

/-! # 指定実分母から恒等分母への実細分辺

概要：任意の実屋根の分母から恒等分母へ、始域成分を指定分母に保つ実辺を構成する。
方針：指定分母と恒等辺の退化合成三角形を実 slice 辺へ戻し、全部分複体に持ち上げる。
規約：終対象性だけによる辺の選択を使わない。使われ方：屋根の評価三角形の全空間への実装。
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

/-- 指定実分母から恒等分母への、元の実分母を始域成分に持つ実細分辺。 -/
def dgActualRoofDenominatorIdentityEdge (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) :
    Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet))
      (dgActualRoofSpanDenominatorVertex A D P x y r) (dgVerdierOverIdentityVertex A D P x) :=
  fullSubcomplexEdgeLift (IsDGVerdierOverVertex A D P x)
    (dgActualRoofSpanDenominatorVertex A D P x y r) (dgVerdierOverIdentityVertex A D P x)
    (roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).edge
    (roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).src_eq
    ((roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).tgt_eq.trans
      (roofPointSliceEdgeVertex_id (X := dgNerve A D) (Simplex.vertex x)))

/-- 指定実細分辺の台は、元の退化合成三角形による実 slice 辺そのもの。 -/
lemma dgActualRoofDenominatorIdentityEdge_simplex (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) :
    (dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌)
      (dgActualRoofDenominatorIdentityEdge A D P x y r).edge =
        (roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).edge :=
  rfl

/-- 指定実細分辺の始域射影は、元の指定実分母の一次単体。 -/
lemma dgActualRoofDenominatorIdentityEdge_source (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) :
    (dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      (dgActualRoofDenominatorIdentityEdge A D P x y r).edge = r.denominator.edge := by
  change (sliceOverProjection
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))).app
      (Opposite.op ⦋1⦌) ((dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌)
        (dgActualRoofDenominatorIdentityEdge A D P x y r).edge) = _
  rw [dgActualRoofDenominatorIdentityEdge_simplex]
  exact roofPointSliceCompositionEdge_projection _

end SerrePositivity.InfinityCategories
