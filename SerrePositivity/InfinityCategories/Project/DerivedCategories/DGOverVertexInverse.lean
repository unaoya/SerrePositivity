module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedRoofVerdierMap

/-! # 実 dg over 頂点から指定閉構造射を回収する

概要：実 slice の頂点を、元の閉零圏の over 対象として表示する。
方針：始点の零単体を対象へ戻し、端点付き実辺と閉零射の同値を使う。
規約：対象と Hom の独立宇宙を保つ。使われ方：厳密屋根比較の零次元の逆表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 実 over 頂点の始点の対象。 -/
def dgOverVertexSource (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌) : D :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _).app (Opposite.op ⦋0⦌) σ).obj 0

/-- 実 over 頂点の回収辺を、元の対象を指定した端点付き辺として読む。 -/
def dgOverVertexEdge (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgOverVertexSource A D x σ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) where
  edge := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ σ).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ σ).src_eq.trans (by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D).injective
    rfl)
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ σ).tgt_eq.trans (Equiv.apply_symm_apply _ _)

/-- 実 over 頂点から回収した閉構造射を持つ通常の over 対象。 -/
def dgOverVertexClosed (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌) : Over (ForgetEnrichment.of (Complex A) x) :=
  Over.mk (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (dgOverVertexEdge A D x σ))

/-- 回収した閉構造射から作った実辺は、指定 slice 頂点の元の実辺。 -/
lemma dgOverVertexClosed_edge (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (dgOverVertexClosed A D x σ).hom).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ σ).edge :=
  congrArg (fun h => h.edge) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_edgeClosed A D (dgOverVertexEdge A D x σ))

/-- 回収した指定閉構造射の実 slice 頂点は、元の実頂点そのもの。 -/
lemma dgOverVertexClosed_vertex (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D (dgOverVertexClosed A D x σ).hom = σ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D (dgOverVertexClosed A D x σ).hom).trans
    (dgOverVertexClosed_edge A D x σ)

/-- 通常の閉 over 比較は零単体上で全射。 -/
lemma dgClosedNerveOverMap_vertex_surjective (x : D) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D x).app (Opposite.op ⦋0⦌)) := by
  intro σ
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (dgOverVertexClosed A D x σ), ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap_vertex A D x _).trans (dgOverVertexClosed_vertex A D x σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
