module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofSliceVertices
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes

/-! # 指定実辺と点上の slice 頂点の相互表示

概要：任意の単体集合の指定辺を、同じ端点を持つ実 slice 頂点へ戻す。
方針：二点の join の同型で辺を移し、頂点の条件と回収辺を照合する。
規約：閉零射の表示を選ばない。使われ方：実屋根合成の頂点を実屋根全空間へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 指定端点の実辺を、その終点上の slice 頂点として表示する。 -/
def roofPointSliceEdgeVertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y)) _⦋0⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target e⟩

/-- 作った slice 頂点の始域は、元の実辺の始点そのもの。 -/
lemma roofPointSliceEdgeVertex_source {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)).app (Opposite.op ⦋0⦌)
      (roofPointSliceEdgeVertex e) = x := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[0] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply]
  exact e.src_eq

/-- 作った slice 頂点から回収した一次単体は、指定した実辺そのもの。 -/
lemma roofPointSliceEdgeVertex_edge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ (roofPointSliceEdgeVertex e)).edge = e.edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge)) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- slice 頂点の回収辺を戻すと、元の頂点を厳密に復元する。 -/
lemma roofPointSliceEdgeVertex_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y)) _⦋0⦌)
    (he : e.edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm y) σ).edge) :
    roofPointSliceEdgeVertex e = σ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  exact (roofPointSliceEdgeVertex_edge e).trans he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
