module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantCoherentTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIsoFacesEquality

/-!
概要：定値な coherent 三角形の指定同型の簡約。
方針：core の包含による定値辺の保存と恒等射を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値な豊穣三角形の関手空間内の代表辺も定値。
方針：core の包含の定値辺に対する自然性を使う。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma spaceInfinityTriangleEdge_constant (s : SpaceInfinity.{u} _⦋2⦌)
    (hs : IsConstantCoherentTriangle s) :
    (spaceInfinityTriangleEdge s).edge = PinchedHom.constant
      (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s))) 1 := by
  change coherentTriangleHomotopy s = _
  rw [coherentTriangleHomotopy_constant_source s hs, kanHom_vertex]
  rfl

/-- 概要：定値な coherent 三角形の指定同型は等式から来る。
方針：指定代表辺の定値性を恒等射の判定に適用する。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma isFunctorEqIso_spaceInfinityTriangleIso (s : SpaceInfinity.{u} _⦋2⦌)
    (hs : IsConstantCoherentTriangle s) : IsFunctorEqIso (spaceInfinityTriangleIso s) :=
  isFunctorEqIso_of_constant_edge _ _ (spaceInfinityTriangleIso_hom s)
    (spaceInfinityTriangleEdge_constant s hs)

end SerrePositivity.InfinityCategories.F2
