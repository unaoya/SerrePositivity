module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTetrahedronFaces

/-! # 実 over 二単体の回収四面体の始点対角辺

概要：回収四面体の対角辺 03 は、元の over 始頂点の指定分母辺そのもの。
方針：一面の四面体回収と、同じ over 辺の始脚回収を接続する。
規約：任意の単体集合で成立。使われ方：四次ホーンの共通始対象の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 回収四面体の始点対角辺は、元の実 over 二単体の始頂点の構造辺。 -/
lemma roofPointSliceTetrahedron_initialDiagonal (t : (sliceOver a) _⦋2⦌) :
    X.δ 1 (X.δ 1 (SSet.yonedaEquiv (roofPointSliceTetrahedron a t))) =
      (roofPointSliceVertexEdge a ((sliceOver a).δ 1 ((sliceOver a).δ 1 t))).edge := by
  have hfirst : X.δ 1 (SSet.yonedaEquiv (roofPointSliceTetrahedron a t)) =
      SSet.yonedaEquiv (roofPointSliceTriangle a ((sliceOver a).δ 1 t)) :=
    (stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTetrahedron a t) 1).symm.trans
      (congrArg (SSet.yonedaEquiv (X := X)) (roofPointSliceTetrahedron_face a t 1))
  exact (congrArg (fun s : X _⦋2⦌ => X.δ 1 s) hfirst).trans
    ((stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTriangle a ((sliceOver a).δ 1 t)) 1).symm.trans
      (roofPointSliceTriangle_leg a ((sliceOver a).δ 1 t) 1))

end SerrePositivity.InfinityCategories
