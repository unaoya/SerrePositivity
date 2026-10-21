module
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeComponent
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCommaCounit
/-!
概要：一般 comma の実余単位の頂点辺を元の同じ閉射へ同定する。
方針：同じ実 prism と反対比較を、一次単体と厳密切断で評価する。
規約：同じ全関手と閉射を保持する。使われ方：一般 RHom の標準写像空間判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

/-- 一般 comma の実余単位ホモトピーの頂点辺は、同じ普遍余単位の閉射。 -/
lemma dgUniversalCommaCounitHomotopy_vertex_edge
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (x : DGUniversalComma R C E F) :
    (simplicialHomotopyVertexEdge (dgUniversalCommaCounitHomotopy R C E F)
      (Simplex.vertex x)).edge =
      (dgClosedEdge R E x.label.universal.counit).edge := by
  let K := DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op
  let A := dgCommaAugmentationSource R Cᵒᵖ Eᵒᵖ F.op
  let B := dgCommaAugmentationTarget R Cᵒᵖ Eᵒᵖ F.op
  let z := dgUniversalCommaDualLabel R C E F x.label
  change (simplicialHomotopyVertexEdge
    (dgNerveOppositeHomotopy R K Eᵒᵖ A B
      (dgCommaAugmentationUnliftedHomotopy R Cᵒᵖ Eᵒᵖ F.op))
    (Simplex.vertex (Opposite.op z))).edge.map (dgDoubleOppositeDown R E) = _
  rw [dgNerveOppositeHomotopy_vertex_edge,
    dgCommaAugmentationUnliftedHomotopy_vertex_edge, opSimplex_dgClosedEdge,
    dgClosedEdge_map]
  rfl
end SerrePositivity.InfinityCategories
