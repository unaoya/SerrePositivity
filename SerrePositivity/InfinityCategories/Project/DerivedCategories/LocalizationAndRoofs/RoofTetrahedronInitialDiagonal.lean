module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTetrahedronFaces

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 回収四面体の始点対角辺は、元の実 over 二単体の始頂点の構造辺。 -/
lemma roofPointSliceTetrahedron_initialDiagonal (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋2⦌) :
    X.δ 1 (X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 t))).edge := by
  have hfirst : X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t)) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 t)) :=
    (stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t) 1).symm.trans
      (congrArg (SSet.yonedaEquiv (X := X)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a t 1))
  exact (congrArg (fun s : X _⦋2⦌ => X.δ 1 s) hfirst).trans
    ((stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 t)) 1).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 t) 1))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
