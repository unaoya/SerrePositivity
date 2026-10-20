module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofSpans
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDenominators

/-! # 任意の実 dg 屋根頂点の合成

概要：元の実屋根全空間の任意の二頂点を、四つの実合成三角形を保って合成する。
方針：実辺 span の回収と復元を、安定 ∞ 圏の実 Ore 細分に接続する。
規約：合成データの存在であり、全空間の厳密な合成関手や結合則はまだ主張しない。
使われ方：商 Hom の実合成三角形と反転関手の作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の二つの指定実屋根頂点に対する、共通細分と四三角形を持つ実合成データ。 -/
abbrev DGActualRoofComposition (P : Set D) (x y z : D)
    (r : (dgRoofCorrespondence A D P x y) _⦋0⦌)
    (s : (dgRoofCorrespondence A D P y z) _⦋0⦌) :=
  ActualRoofComposition (dgVerdierEdges A D P)
    (dgActualRoofVertexSpan A D P x y r) (dgActualRoofVertexSpan A D P y z s)

/-- 任意の二つの指定実屋根頂点は、元の実辺を保持する実合成データを持つ。 -/
theorem dgActualRoofComposition_nonempty [Small.{u} D] [IsDGPretriangulated A D]
    (P : Set D) (x y z : D) (r : (dgRoofCorrespondence A D P x y) _⦋0⦌)
    (s : (dgRoofCorrespondence A D P y z) _⦋0⦌) :
    Nonempty (DGActualRoofComposition A D P x y z r s) := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact cofiberStableEdges_actualRoofComposition_nonempty (X := dgNerve A D) (Simplex.vertex '' P)
    (dgActualRoofVertexSpan A D P x y r) (dgActualRoofVertexSpan A D P y z s)

/-- 実合成データから、元の実屋根全空間内の合成頂点を得る。 -/
def dgActualRoofCompositeVertex (P : Set D) (x y z : D)
    {r : (dgRoofCorrespondence A D P x y) _⦋0⦌}
    {s : (dgRoofCorrespondence A D P y z) _⦋0⦌}
    (C : DGActualRoofComposition A D P x y z r s) :
    (dgRoofCorrespondence A D P x z) _⦋0⦌ :=
  dgActualRoofSpanVertex A D P x z C.composite

/-- 実合成頂点の回収分子は、実合成データで指定した合成分子そのもの。 -/
lemma dgActualRoofCompositeVertex_numerator (P : Set D) (x y z : D)
    {r : (dgRoofCorrespondence A D P x y) _⦋0⦌}
    {s : (dgRoofCorrespondence A D P y z) _⦋0⦌}
    (C : DGActualRoofComposition A D P x y z r s) :
    (roofPointSliceVertexEdge _
      ((dgRoofCorrespondenceTarget A D P x z).app (Opposite.op ⦋0⦌)
        (dgActualRoofCompositeVertex A D P x y z C))).edge = C.combinedNumerator.edge := by
  rw [dgActualRoofCompositeVertex, dgActualRoofSpanVertex_target]
  exact roofPointSliceEdgeVertex_edge _

/-- 実合成頂点の回収分母は、実合成データで指定した合成分母そのもの。 -/
lemma dgActualRoofCompositeVertex_denominator (P : Set D) (x y z : D)
    {r : (dgRoofCorrespondence A D P x y) _⦋0⦌}
    {s : (dgRoofCorrespondence A D P y z) _⦋0⦌}
    (C : DGActualRoofComposition A D P x y z r s) :
    (roofPointSliceVertexEdge _
      ((dgRoofCorrespondenceProjection A D P x z).app (Opposite.op ⦋0⦌)
        (dgActualRoofCompositeVertex A D P x y z C)).val).edge = C.combinedDenominator.edge := by
  rw [dgActualRoofCompositeVertex, dgActualRoofSpanVertex_projection]
  exact roofPointSliceEdgeVertex_edge _

end SerrePositivity.InfinityCategories
