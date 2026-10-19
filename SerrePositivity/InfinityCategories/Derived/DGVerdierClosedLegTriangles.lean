module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEqualityTransport
public import SerrePositivity.InfinityCategories.Derived.DGVerdierClosedVertexRefinement
public import SerrePositivity.InfinityCategories.Derived.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Derived.DGTriangleSourceRefinementCongruence

/-! # 同じ閉分母で細分した頂点ごとの固定脚三角形

概要：元の頂点錐と追加実閉分母だけから、各頂点の同じ細分脚三角形を固定する。
方針：零面を保ち、対角辺を共通閉細分分母の実辺へ同定する。
規約：辺族に依存しない。使われ方：高次の各辺錐の二脚の共通化。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable {C : DGVerdierDiagramVertexCone A D P x f}
variable (R : DGVerdierClosedVertexRefinement A D C)

/-- 各頂点の元の脚三角形を、同じ一つの追加実閉分母で細分する。 -/
def DGVerdierClosedVertexRefinement.legTriangle (v : K _⦋0⦌) : Simplex A D 2 :=
  dgSimplexSourceRefinement (dgVerdierDiagramLegTriangle A D C v) R.q
    (dgClosedTargetTransport A D R.s (dgVerdierDiagramLegTriangle_source A D C v).symm)

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 頂点ごとの同じ細分脚三角形は、元の指定終頂点の分母辺を零面に保つ。 -/
lemma DGVerdierClosedVertexRefinement.legTriangle_face0 (v : K _⦋0⦌) :
    (dgNerve A D).δ 0 (DGVerdierClosedVertexRefinement.legTriangle A D R v) =
      (roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) (f.app _ v).val).edge :=
  (dgSimplexSourceRefinement_face0 _ _ _).trans (dgVerdierDiagramLegTriangle_face0 A D C v)

/-- 各細分脚三角形の対角辺は、同じ一つの共通閉細分頂点の分母辺。 -/
lemma DGVerdierClosedVertexRefinement.legTriangle_face1 (v : K _⦋0⦌) :
    (dgNerve A D).δ 1 (DGVerdierClosedVertexRefinement.legTriangle A D R v) =
      (roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) R.commonApex.val).edge := by
  let g := dgSimplexClosedDiagonal A D (dgVerdierDiagramLegTriangle A D C v)
  have hg : (dgClosedEdge A D g).edge = (dgClosedEdge A D C.denominator.obj.hom).edge :=
    (dgSimplexClosedDiagonal_edge A D (dgVerdierDiagramLegTriangle A D C v)).symm.trans
      (dgVerdierDiagramLegTriangle_diagonal A D C v)
  have hc := dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (Complex A) C.denominator.obj.left) (y' := x)
    (dgClosedTargetTransport A D R.s (dgVerdierDiagramLegTriangle_source A D C v).symm) R.s
    g C.denominator.obj.hom (dgClosedTargetTransport_edge A D R.s _) hg
  exact (dgSimplexSourceRefinement_face1_comp A D (dgVerdierDiagramLegTriangle A D C v) R.q
    (dgClosedTargetTransport A D R.s (dgVerdierDiagramLegTriangle_source A D C v).symm)).trans
      (hc.trans (dgClosedOverVertex_edge A D R.commonDenominator.obj.hom).symm)

end SerrePositivity.InfinityCategories
